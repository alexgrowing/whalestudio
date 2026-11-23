import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel

noncomputable section

namespace GlobalTheory.SerSys

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

structure Sys (g : ℕ) [Fact g.Prime] where
  e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)
  idem : ∀ n f, e n f * e n f = e n f
  central : ∀ n f a, e n f * a = a * e n f
  orth : ∀ n f f', f ≠ f' → e n f * e n f' = 0
  label : ∀ n f, e n f ≠ 0 → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0
  sum : ∀ n, ∃ T : Finset (ZMod g)[X], ∑ f ∈ T, e n f = 1

  mul : ∀ (a b n : ℕ), n = a + b → ∀ (f f' : (ZMod g)[X]) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Gn g n) V) (v : V),
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → ρ u v = v) →
    ∑ x : Gn g a, (e a f).coeff x • ρ (blk a b n x 1) v = v →
    ∑ y : Gn g b, (e b f').coeff y • ρ (blk a b n 1 y) v = v →
    ρ.asAlgebraHom (e n (f * f')) v = v

variable {g : ℕ} [Fact g.Prime]

def Has (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (f : (ZMod g)[X]) : Prop :=
  ∃ v ∈ fixK1 π, actK π (S.e n f) v ≠ 0

def CharIn (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) (h : (ZMod g)[X]) : Prop :=
  ∑ y : Gn g b, (S.e b h).coeff y * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) ≠ 0

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

def IneUnr (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.unr χ →
    ∀ s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.lpChar a χ) s = D.naut.inePol a s

def LocType (D : D7) (S : ∀ k, Sys (D.host.g k)) : Prop :=
  ∀ (i : D.nd.Loc) (P : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
    ∃ (π : Rep.{0} ℂ (GL (Fin D.R.nV) ℚ_[D.host.g k])) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ) (c : ZMod (D.host.g k)),
      (∀ F ∈ D.naut.typeV i P, ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)),
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v a) F ≠ 0 →
        ∃ u, IsParVec π.ρ D.R.r D.R.t χ u ∧ actTop π.ρ D.R.r D.R.t a u ≠ 0) ∧
      CharIn (S k) χ D.R.t ((X - C c) ^ D.R.t) ∧
      D.naut.inePol (D.naut.locG (D.naut.muC i) (D.naut.plGw k v)) (D.ntypes.tg k v) =
        X - C (D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c)) ∧
      ∀ f, Has (S k) π.ρ f → D.naut.inePol (D.naut.locV i P (D.naut.plGw k v)) (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod

def Sys.IsOf (S : Sys g) (L : LabelDatum g) : Prop := ∀ n f, S.e n f = eSerC L n f

theorem Sys.IsOf.has_iff {S : Sys g} {L : LabelDatum g} (h : S.IsOf L) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X]) : Has S π f ↔ HasLab L π f := by
  rw [Has, h]; rfl

abbrev QRep (g : ℕ) [Fact g.Prime] (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[g])

def IrrSm {n : ℕ} (π : QRep g n) : Prop := IsIrrRep π.ρ ∧ GlobalTheory.PRep.IsSmooth π.ρ

def TamePart (μ : ℚ_[g]ˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, μ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
    χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u)

def ActsThrough {n : ℕ} (π : QRep g n) (r t : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (W : Submodule ℂ M) (act : MonoidAlgebra ℂ (Gn g r) → Module.End ℂ M) : Prop :=
  ∃ (J : Type) (ι : W →ₗ[ℂ] (J → π)), Function.Injective ι ∧ (∀ F j, IsParVec π.ρ r t χ (ι F j)) ∧
    ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn g r)), ∀ F : W,
      ∃ h : act a F ∈ W, ∀ j, ι ⟨act a F, h⟩ j = actTop π.ρ r t a (ι F j)

def IsClassMap {LP : Type*} (dim : LP → ℕ) (rc : ∀ n, QRep g n → LP) : Prop :=
  ∀ n (π : QRep g n), IrrSm π → dim (rc n π) = n ∧ ∀ π' : QRep g n, IrrSm π' → (rc n π = rc n π' ↔ Nonempty (π ≅ π'))

def SerParam (e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ine : ∀ n, QRep g n → ℂ[X]) : Prop :=
  ∀ n (π : QRep g n), IrrSm π → ∀ f, (∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0) →
    ine n π = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod

abbrev Corr (D : D7) : Type 1 :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (n : ℕ), QRep (D.host.g k) n → D.naut.LP (D.naut.plGw k v)

def SysTie (D : D7) (S : ∀ k, Sys (D.host.g k)) : Prop := ∀ k f, D.ntypes.eSer k f = (S k).e D.R.r f

def LabTie (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) : Prop :=
  ∀ k, (L k).teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = eSerC (L k) D.R.r f

def LocComp (D : D7) (rc : Corr D) : Prop :=
  (∀ k v, IsClassMap D.naut.lpDim (rc k v)) ∧
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ),
    TamePart μ χ ∧ D.naut.locG (D.naut.muC i) (D.naut.plGw k v) = rc k v 1 (Rep.of (Model.detRep 1 μ)) ∧
    ∀ P : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧
      D.naut.locV i P (D.naut.plGw k v) = rc k v D.R.nV π ∧
      ActsThrough π D.R.r D.R.t χ (D.naut.typeV i P) fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v a)

def LabParam (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) : Prop :=
  ∀ k v, SerParam (eSerC (L k)) (L k).teich fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)

theorem eSerTie_iff (D : D7) : ESerTie D ↔ ∃ L, LabTie D L :=
  ⟨fun h => ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩, fun ⟨L, h⟩ k => ⟨L k, h k⟩⟩

theorem LabTie.sysTie {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} (h : LabTie D L)
    (hS : ∀ k, (S k).IsOf (L k)) : SysTie D S := fun k f => ((h k).2 f).trans (hS k _ f).symm

namespace Loc

open Matrix.GeneralLinearGroup

theorem alg_sum {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem det_blocks (a b : ℕ) (x : Gn g a) (y : Gn g b) : det (blk a b (a + b) x y) = det x * det y := by
  set M : Mt g (a + b) := fun i j : Fin (a + b) =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN (y : Mt g b) (i - a) (j - a) else 0 with hM
  have h0 : InPar a M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl a M = x := by
    ext i j
    have hi : (i : ℕ) < a + b := by omega
    have hj : (j : ℕ) < a + b := by omega
    simp [tl, entN, hM, hi, hj]
  have h2 : br a b M = y := by
    ext i j
    simp [br, entN, hM]
  have hd := LabelDet.det_inPar a b M h0
  rw [h1, h2] at hd
  apply Units.ext
  change ((det (toG M) : (ZMod g)ˣ) : ZMod g) = _
  rw [LabelDet.det_toG M (hd ▸ mul_ne_zero x.det_ne_zero y.det_ne_zero), hd]
  simp

theorem det_rad {a b : ℕ} {u : Gn g (a + b)} (h0 : InPar a (u : Mt g (a + b))) (h1 : tl a (u : Mt g (a + b)) = 1)
    (h2 : br a b (u : Mt g (a + b)) = 1) : det u = 1 := by
  rw [LabelDet.det_par a b u h0, h1, h2, LabelDet.toG_one, LabelDet.toG_one]; simp

def ev (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) : ℂ := ∑ y : Gn g n, a.coeff y * ((χ (det y) : ℂˣ) : ℂ)

theorem alg_ev (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) (v : ℂ) :
    (Model.chRep (χ.comp (det (n := Fin n)))).asAlgebraHom a v = ev χ a * v := by
  rw [alg_sum, ev, Finset.sum_mul]
  simp [mul_assoc]

theorem charIn_iff (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) (h : (ZMod g)[X]) :
    CharIn S χ b h ↔ ev χ (S.e b h) = 1 := by
  change ev χ (S.e b h) ≠ 0 ↔ _
  refine ⟨fun h0 => ?_, fun h1 => h1 ▸ one_ne_zero⟩
  have := alg_ev χ (S.e b h * S.e b h) 1
  rw [map_mul, Module.End.mul_apply, alg_ev, alg_ev, S.idem] at this
  exact mul_left_cancel₀ h0 (by simpa using this)

theorem exists_charIn (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) :
    ∃ h, CharIn S χ b h ∧ h.Monic ∧ h.natDegree = b ∧ h.coeff 0 ≠ 0 := by
  obtain ⟨T, hT⟩ := S.sum b
  have h1 := congrArg (fun a => (Model.chRep (χ.comp (det (n := Fin b)))).asAlgebraHom a 1) hT
  simp only [map_sum, LinearMap.sum_apply, alg_ev, map_one, Module.End.one_apply, mul_one] at h1
  obtain ⟨h, -, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
  exact ⟨h, hh, S.label b h fun e => hh (by rw [e]; simp [ev])⟩

theorem charIn_mul (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) {a b : ℕ} {f f' : (ZMod g)[X]} (h : CharIn S χ a f)
    (h' : CharIn S χ b f') : CharIn S χ (a + b) (f * f') := by
  rw [charIn_iff] at h h' ⊢
  have := S.mul a b _ rfl f f' ℂ (Model.chRep (χ.comp (det (n := Fin (a + b))))) 1
    (fun u h0 h1 h2 => by simp [det_rad h0 h1 h2]) (by simpa [det_blocks, ev] using h) (by simpa [det_blocks, ev] using h')
  rwa [alg_ev, mul_one] at this

theorem charIn_pow (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) {h : (ZMod g)[X]} (h1 : CharIn S χ 1 h) (b : ℕ) :
    CharIn S χ b (h ^ b) := by
  induction b with
  | zero =>
    obtain ⟨f, hf, hm, hd, -⟩ := exists_charIn S χ 0
    rwa [hm.natDegree_eq_zero.1 hd, ← pow_zero h] at hf
  | succ b ih => exact pow_succ h b ▸ charIn_mul S χ ih h1

theorem tamePart_tame (χ : (ZMod g)ˣ →* ℂˣ) : TamePart (Model.tame χ) χ := fun u => by
  rw [Model.tame, MonoidHom.comp_apply, MonoidHom.comp_apply, Model.unitPart_unit]

section Det

variable {μ : ℚ_[g]ˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ} (h : TamePart μ χ) {n : ℕ}
include h

theorem det_inc (k : GL (Fin n) ℤ_[g]) : μ (det (inc g n k)) = χ (det (red g n k)) := by
  have h1 : det (inc g n k) = Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (det k) := by
    ext; simp [inc, RingHom.map_det]
  have h2 : det (red g n k) = Units.map (PadicInt.toZMod (p := g)).toMonoidHom (det k) := by
    ext; simp [red, RingHom.map_det]
  rw [h1, h2, h]

theorem detCharacter_mem_principalCongruenceFixedVectors (v : ℂ) : v ∈ fixK1 (Model.detRep n μ) := by
  rw [Model.mem_principalCongruenceFixedVectors_iff]; intro k hk
  simp [Model.detRep, det_inc h, hk]

theorem det_lift (x : Gn g n) (v : ℂ) : Model.detRep n μ (lift g n x) v = χ (det x) * v := by
  obtain ⟨k, rfl⟩ := Model.red_surjective n x
  rw [Model.lift_red _ (detCharacter_mem_principalCongruenceFixedVectors h v)]
  simp [Model.detRep, det_inc h]

theorem actK_det (a : MonoidAlgebra ℂ (Gn g n)) (v : ℂ) : actK (Model.detRep n μ) a v = ev χ a * v := by
  simp [actK, LinearMap.sum_apply, det_lift h, ev, Finset.sum_mul, mul_assoc]

theorem has_det (S : Sys g) (f : (ZMod g)[X]) : Has S (Model.detRep n μ) f ↔ CharIn S χ n f := by
  refine ⟨fun ⟨v, _, hv⟩ => ?_, fun hf => ⟨1, detCharacter_mem_principalCongruenceFixedVectors h 1, by rwa [actK_det h, mul_one]⟩⟩
  rw [actK_det h] at hv
  exact left_ne_zero_of_mul hv

theorem irrSm_det : IrrSm (Rep.of (Model.detRep n μ)) := by
  refine ⟨Model.isIrrRep_chRep _, fun (v : ℂ) => ?_⟩
  let H : Subgroup (GL (Fin n) ℚ_[g]) :=
    { carrier := {x | Model.detRep n μ x v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change Model.detRep n μ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change Model.detRep n μ a⁻¹ v = v
        conv_lhs => rw [← show Model.detRep n μ a v = v from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hc : Continuous fun x : GL (Fin n) ℚ_[g] => ‖x.val.det - 1‖ :=
    ((Units.continuous_val.matrix_det).sub continuous_const).norm
  refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset
    ((isOpen_lt hc continuous_const).mem_nhds (show ‖(1 : GL (Fin n) ℚ_[g]).val.det - 1‖ < 1 by simp)) fun x hx => ?_)
  have hx' : ‖x.val.det - 1‖ < 1 := hx
  have h1 : ‖x.val.det‖ = 1 := by
    have := Padic.norm_eq_of_norm_sub_lt_right (z1 := x.val.det) (z2 := 1) (by simpa using hx')
    simpa using this
  have e1 : det x = Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (PadicInt.mkUnits h1) := by
    ext; simp; rfl
  have e2 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom (PadicInt.mkUnits h1) = 1 := by
    have : ((PadicInt.mkUnits h1 : ℤ_[g]ˣ) : ℤ_[g]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx'
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact Units.ext this
  change Model.detRep n μ x v = v
  simp only [Model.detRep, Model.chRep_apply, MonoidHom.comp_apply]
  rw [e1, h, e2]; simp

theorem isParVec_det (r t : ℕ) (v : ℂ) : IsParVec (Model.detRep (r + t) μ) r t χ v :=
  ⟨detCharacter_mem_principalCongruenceFixedVectors h v, fun u h0 h1 h2 => by rw [det_lift h, det_rad h0 h1 h2]; simp,
    fun y => by rw [det_lift h, det_blocks]; simp⟩

theorem actsThrough_det (r t : ℕ) :
    ActsThrough (Rep.of (Model.detRep (r + t) μ)) r t χ (⊤ : Submodule ℂ ℂ) fun a => ev χ a • LinearMap.id := by
  refine ⟨Unit, LinearMap.pi fun _ => (⊤ : Submodule ℂ ℂ).subtype, fun x y e => Subtype.ext (congrFun e ()),
    fun F _ => isParVec_det h r t _, fun a _ F => ⟨trivial, fun _ => ?_⟩⟩
  change ev χ a * F.1 = actTop (Model.detRep (r + t) μ) r t a F.1
  simp [actTop, LinearMap.sum_apply, det_lift h, det_blocks, ev, Finset.sum_mul, mul_assoc]

theorem act_eq_of_actsThrough_det {r t : ℕ} {χ' : (ZMod g)ˣ →* ℂˣ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {W : Submodule ℂ M} {act : MonoidAlgebra ℂ (Gn g r) → Module.End ℂ M}
    (H : ActsThrough (Rep.of (Model.detRep (r + t) μ)) r t χ' W act) {a : MonoidAlgebra ℂ (Gn g r)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn g r))) {F : M} (hF : F ∈ W) : act a F = ev χ a • F := by
  obtain ⟨J, ι, hi, -, he⟩ := H
  obtain ⟨hm, hj⟩ := he a ha ⟨F, hF⟩
  refine congrArg Subtype.val (hi (a₁ := ⟨_, hm⟩) (a₂ := ev χ a • ⟨F, hF⟩) (funext fun j => ?_))
  rw [hj, map_smul, Pi.smul_apply]
  generalize ι ⟨F, hF⟩ j = z
  change actTop (Model.detRep (r + t) μ) r t a (z : ℂ) = ev χ a * (z : ℂ)
  simp [actTop, LinearMap.sum_apply, det_lift h, det_blocks, ev, Finset.sum_mul, mul_assoc]

end Det

theorem prod_linear (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (c : ZMod g) :
    ((Formalism.CyclotomicNorms.rootsBar (X - C c)).map fun x => X - C (τ x)).prod =
      X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)) := by
  simp [Formalism.CyclotomicNorms.rootsBar]

theorem exists_serParam (e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (h : ∀ n (π : QRep g n), IrrSm π → ∀ f f', (∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0) →
      (∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f') v ≠ 0) → f = f') : ∃ ine, SerParam e τ ine :=
  ⟨fun n π => ((Formalism.CyclotomicNorms.rootsBar (Classical.epsilon fun f => ∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0)).map
      fun x => X - C (τ x)).prod,
    fun n π hπ f hf => by
      rw [h n π hπ f _ hf (Classical.epsilon_spec (p := fun f => ∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0) ⟨f, hf⟩)]⟩

theorem isClassMap_mk : IsClassMap (LP := Σ n, Quotient (CategoryTheory.isIsomorphicSetoid (QRep g n))) Sigma.fst
    fun n π => ⟨n, Quotient.mk _ π⟩ := fun n π _ =>
  ⟨rfl, fun π' _ => by rw [Sigma.mk.inj_iff, heq_eq_eq, Quotient.eq]; exact and_iff_right rfl⟩

def coarse (g : ℕ) [Fact g.Prime] : Sys g where
  e n f := if f = (X - C 1) ^ n then 1 else 0
  idem n f := by split_ifs <;> simp
  central n f a := by split_ifs <;> simp
  orth n f f' h := by
    split_ifs with h1 h2
    · exact absurd (h1.trans h2.symm) h
    all_goals simp
  label n f h := by
    have hf : f = (X - C 1) ^ n := by by_contra hf; exact h (if_neg hf)
    subst hf
    refine ⟨(monic_X_sub_C _).pow n, by rw [natDegree_pow, natDegree_X_sub_C, mul_one], ?_⟩
    rw [coeff_zero_eq_eval_zero]; simp
  sum n := ⟨{(X - C 1) ^ n}, by simp⟩
  mul a b n hn f f' V _ _ ρ v _ h1 h2 := by
    by_cases e1 : f = (X - C 1) ^ a
    · by_cases e2 : f' = (X - C 1) ^ b
      · rw [if_pos (by rw [e1, e2, hn, pow_add])]; simp
      · rw [if_neg e2] at h2
        have : v = 0 := by simpa using h2.symm
        simp [this]
    · rw [if_neg e1] at h1
      have : v = 0 := by simpa using h1.symm
      simp [this]

end Loc

theorem ActsThrough.exists_parVec {n r t : ℕ} {π : QRep g n} {χ : (ZMod g)ˣ →* ℂˣ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {W : Submodule ℂ M} {act : MonoidAlgebra ℂ (Gn g r) → Module.End ℂ M} (H : ActsThrough π r t χ W act) {F : M}
    (hF : F ∈ W) {a : MonoidAlgebra ℂ (Gn g r)} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn g r)))
    (h0 : act a F ≠ 0) : ∃ u, IsParVec π.ρ r t χ u ∧ actTop π.ρ r t a u ≠ 0 := by
  obtain ⟨J, ι, hi, hp, he⟩ := H
  obtain ⟨hm, hj⟩ := he a ha ⟨F, hF⟩
  obtain ⟨j, h1⟩ := Function.ne_iff.1 ((map_ne_zero_iff ι hi).2 (fun e => h0 (congrArg Subtype.val e) : (⟨_, hm⟩ : W) ≠ 0))
  exact ⟨_, hp _ j, hj j ▸ h1⟩

theorem Sys.IsOf.charIn_one {S : Sys g} {L : LabelDatum g} (h : S.IsOf L) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (hc : IsCharLab L χ c) (χ' : (ZMod g)ˣ →* ℂˣ) : CharIn S χ' 1 (X - C c) ↔ χ' = χ := by
  rw [← Loc.has_det (Loc.tamePart_tame χ'), h.has_iff, Model.hasLab_tame L hc]

theorem Sys.IsOf.charIn {S : Sys g} {L : LabelDatum g} (h : S.IsOf L) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (hc : IsCharLab L χ c) (b : ℕ) : CharIn S χ b ((X - C c) ^ b) :=
  Loc.charIn_pow S χ ((h.charIn_one hc χ).2 rfl) b

theorem Loc.not_isOf_coarse (hg : g ≠ 2) (L : LabelDatum g) : ¬ (Loc.coarse g).IsOf L := by
  intro h
  obtain ⟨u, hu, ho⟩ := Model.exists_gen L
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hc : IsCharLab L T.toHomUnits u := ⟨u.ne_zero, fun w hw => by rw [hu, ← hw]; rfl⟩
  have h1 := (h.charIn_one hc _).2 rfl
  have h2 : X - C (u : ZMod g) = (X - C 1) ^ 1 := by
    by_contra e
    apply h1
    change ∑ y : Gn g 1, (if X - C (u : ZMod g) = (X - C 1) ^ 1 then (1 : MonoidAlgebra ℂ (Gn g 1)) else 0).coeff y * _ = 0
    rw [if_neg e]; simp
  rw [pow_one, sub_right_inj, C_inj, Units.val_eq_one] at h2
  rw [h2, orderOf_one] at ho
  have := (Fact.out : g.Prime).two_le
  omega

theorem LabParam.char {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {rc : Corr D} (h : LabParam D L rc) (k : Fin 2)
    (v : D.nd.PlG k) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ) (u : (ZMod (D.host.g k))ˣ)
    (hu : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u = (L k).gen 1) :
    D.naut.inePol (rc k v 1 (Rep.of (Model.detRep 1 (Model.tame χ)))) (D.ntypes.tg k v) = X - C ((χ u : ℂˣ) : ℂ) := by
  obtain ⟨c, hc⟩ := Model.isCharLab_exists (L k) χ
  rw [hc.2 u hu, ← Loc.prod_linear]
  exact h k v 1 _ (Loc.irrSm_det (Loc.tamePart_tame χ)) _ ((Model.hasLab_tame (L k) hc χ).2 rfl)

theorem locType_of_serParam {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : LocComp D rc)
    (hP : ∀ k v, SerParam (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)

theorem locType_of_ties {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : LocComp D rc) (hP : LabParam D L rc) : LocType D S :=
  locType_of_serParam hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from funext fun n => funext (hS k n)]
    exact hP k v

end GlobalTheory.SerSys
