import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cmHost_imaginaryGenerator_ne_zero : D.host.xi0 ≠ 0 := by
  have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
  have h2 : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have := D.host.sqrtMinusD_sq
    rw [h] at this
    have hd : (D.host.d : D.host.E) ≠ 0 := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : D.host.d ≠ 0)
    apply hd
    linear_combination this
  unfold Formalism.BasicNotions.Host.xi0
  exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)

@[reducible] def negSp (V : HSp D) : HSp D where
  V := V.V
  hT := -V.hT
  herm := ⟨fun x y => by
    simp only [LinearMap.neg_apply, map_neg]
    rw [V.herm.eq]⟩
  nondeg := ⟨fun x hx => V.nondeg.1 x fun y => by simpa using hx y, fun y hy => V.nondeg.2 y fun x => by simpa using hy x⟩
  rank := V.rank
  rank_eq := V.rank_eq
  frame := V.frame
  sig := fun τ => (V.sig τ).swap
  L0 := V.L0
  standardTuple_isLattice := V.standardTuple_isLattice
  baseLattice_isUnimodular := by
    have h := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at h ⊢
    refine Eq.trans ?_ h
    ext x
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.neg_apply, neg_mem_iff]

theorem negSp_gram (V : HSp D) : (negSp V).gram = -V.gram := rfl

theorem HR_neg (V : HSp D) :
    HR (AF D.host.F) D.sp.cm.sig V.gram = HR (AF D.host.F) D.sp.cm.sig (negSp V).gram := by
  ext g
  have e : JR (F := D.host.F) (AF D.host.F) (-V.gram) = -JR (F := D.host.F) (AF D.host.F) V.gram := by
    ext i j; simp [JR]
  show Formalism.UG.cT _ g.1 * JR (AF D.host.F) V.gram * g.1 = JR (AF D.host.F) V.gram ↔
    Formalism.UG.cT _ g.1 * JR (AF D.host.F) (-V.gram) * g.1 = JR (AF D.host.F) (-V.gram)
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def negGA (V : HSp D) : GA D V ≃* GA D (negSp V) := MulEquiv.subgroupCongr (HR_neg V)

theorem mt_negGA (V : HSp D) (g : GA D V) : mt (negSp V) (negGA V g) = mt V g := rfl

theorem continuous_negGA (V : HSp D) : Continuous (negGA V) :=
  Continuous.subtype_mk (continuous_subtype_val (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)) _

theorem isSelfDualC_neg {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSelfDualC V Λ) :
    IsSelfDualC (negSp V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (negSp V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

variable (D) in

structure LSp where

  sp : HSp D

  lat : Submodule (𝓞 D.host.E) (Fin sp.rank → D.host.E)

structure LSp.IsV (X : LSp D) (ν q : ℕ) : Prop where

  rank : X.sp.rank = ν

  sigOK : X.sp.SigOK

  sig : ∀ τ, X.sp.sig τ = (ν - q, q)

  sd : IsSelfDualC X.sp X.lat

def antiDiagonalSignGramMatrix {R : Type} [Zero R] [One R] (c : ℕ) (ε : R) : Matrix (Fin c) (Fin c) R :=
  fun p q => if p.1 + q.1 + 1 = c then (if p = q then ε else 1) else 0

structure HermitianOrthogonalExtensionData (A B : HSp D) (c : ℕ) (ε : D.host.E) where

  ι : A.V →ₗ[D.host.E] B.V

  isom : HSpace.IsIsomEmb A B ι

  a : Matrix (Fin B.rank) (Fin c) D.host.E

  gram : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) a * B.gram * a = antiDiagonalSignGramMatrix c ε

  perp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * a = 0

  rank : A.rank + c = B.rank

def sumLat {n k c : ℕ} (M : Matrix (Fin n) (Fin k) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E))
    (a : Matrix (Fin n) (Fin c) D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) where
  carrier := {x | ∃ y ∈ Λ, ∃ u : Fin c → D.host.E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u}
  zero_mem' := ⟨0, Λ.zero_mem, 0, fun p => (𝔟 p).zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, u, hu, rfl⟩ ⟨y', hy', u', hu', rfl⟩
    refine ⟨y + y', Λ.add_mem hy hy', u + u', fun p => (𝔟 p).val.add_mem (hu p) (hu' p), ?_⟩
    rw [mulVec_add, mulVec_add]; abel
  smul_mem' := by
    rintro r _ ⟨y, hy, u, hu, rfl⟩
    refine ⟨r • y, Λ.smul_mem r hy, r • u, fun p => (𝔟 p).val.smul_mem r (hu p), ?_⟩
    rw [mulVec_smul, mulVec_smul, smul_add]

def stairId (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (c : ℕ) (p : Fin c) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  𝔞 ^ (c - p.1) * (𝔞' ^ (p.1 + 1))⁻¹

theorem stairId_succ {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h : 𝔞' ≠ 0) {c : ℕ} (p q : Fin c)
    (hpq : q.1 = p.1 + 1) : stairId 𝔞 𝔞' c p = 𝔞 * 𝔞' * stairId 𝔞 𝔞' c q := by
  have h1 : c - p.1 = (c - q.1) + 1 := by have := q.2; omega
  unfold stairId
  rw [h1, hpq, pow_succ 𝔞' (p.1 + 1), pow_succ 𝔞]
  field_simp

theorem stairId_rev (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {c : ℕ} (p : Fin c) :
    stairId 𝔞' 𝔞 c p.rev = (stairId 𝔞 𝔞' c p)⁻¹ := by
  have h1 : c - p.rev.1 = p.1 + 1 := by have := p.2; rw [Fin.val_rev]; omega
  have h2 : p.rev.1 + 1 = c - p.1 := by have := p.2; rw [Fin.val_rev]; omega
  unfold stairId
  rw [h1, h2, mul_inv, inv_inv, mul_comm]

namespace HermitianOrthogonalExtensionData

variable {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)

def lat (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E) :=
  sumLat (frameMat B A d.ι) Λ d.a 𝔟

def iso (ρ : ℕ) (h : 2 * ρ ≤ c) : Matrix (Fin B.rank) (Fin ρ) D.host.E :=
  d.a.submatrix id (Fin.castLE (by omega))

theorem gram_sub {k l : ℕ} (f : Fin k → Fin c) (g : Fin l → Fin c) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (d.a.submatrix id f) * B.gram * d.a.submatrix id g =
      (antiDiagonalSignGramMatrix c ε).submatrix f g := by
  rw [← d.gram]; rfl

theorem isIsoSub_iso (ρ : ℕ) (h : 2 * ρ ≤ c) : IsIsoSub B (d.iso ρ h) := by
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun u hu i => ?_
    have h1 : d.iso ρ h *ᵥ u = 0 := by
      rw [← hu]; funext k; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have h2 := d.gram_sub (fun q : Fin ρ => (Fin.castLE (by omega) q : Fin c).rev) (Fin.castLE (by omega) : Fin ρ → Fin c)
    have h3 : (antiDiagonalSignGramMatrix c ε).submatrix (fun q : Fin ρ => (Fin.castLE (by omega) q : Fin c).rev)
        (Fin.castLE (by omega) : Fin ρ → Fin c) = 1 := by
      refine Matrix.ext fun p q => ?_
      have := p.2; have := q.2
      simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, one_apply, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    have h4 := congrArg (· *ᵥ u) (h2.trans h3)
    simp only [one_mulVec, ← mulVec_mulVec] at h4
    rw [show d.a.submatrix id (Fin.castLE (by omega) : Fin ρ → Fin c) = d.iso ρ h from rfl, h1, mulVec_zero,
      mulVec_zero] at h4
    exact (congrFun h4 i).symm
  · refine (d.gram_sub _ _).trans ?_
    refine Matrix.ext fun p q => ?_
    have := p.2; have := q.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]

def besDat (hε : ε ≠ 0) (ρ : ℕ) (h : c = 2 * ρ + 1) : BesDat A B d.ι where
  ρ := ρ
  codim := by have := d.rank; omega
  e := d.iso ρ (by omega)
  e_iso := d.isIsoSub_iso ρ _
  e_perp := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun d.perp i) (Fin.castLE (by omega) j)
  z := fun k => d.a k ⟨ρ, by omega⟩
  z_perpA := by
    funext i
    exact congrFun (congrFun d.perp i) ⟨ρ, by omega⟩
  z_perpE := by
    funext i
    have h1 := congrFun (congrFun d.gram (Fin.castLE (by omega) i)) ⟨ρ, by omega⟩
    refine h1.trans ?_
    have := i.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_castLE, Pi.zero_apply]
    rw [if_neg (by omega)]
  z_ne := by
    have h1 := congrFun (congrFun d.gram ⟨ρ, by omega⟩) ⟨ρ, by omega⟩
    simp only [antiDiagonalSignGramMatrix, if_true] at h1
    rw [if_pos (by omega)] at h1
    intro h0
    apply hε
    rw [← h1, ← h0, Formalism.UG.hform, Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul, Formalism.UG.cT, transpose_apply, map_apply]
  c := fun _ => D.host.xi0
  c_ne := fun _ => cmHost_imaginaryGenerator_ne_zero
  y := 1

end HermitianOrthogonalExtensionData

section Cong

open Formalism.L2.Herm Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

def congLev (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) :
    Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) where
  carrier := {g | g ∈ UA hc J ∧ g ∈ Formalism.UG.stabGL (hatL (F := F) Λ) ∧
    ∀ x ∈ hatL (F := F) Λ, g.1 *ᵥ x - x ∈ hatL (F := F) (𝔪 • Λ)}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    refine ⟨Subgroup.mul_mem _ g1 h1, Subgroup.mul_mem _ g2 h2, fun x hx => ?_⟩
    have := Submodule.add_mem _ (g3 _ ((h2 x).1 hx)) (h3 x hx)
    rw [Units.val_mul, ← mulVec_mulVec]
    simpa using this
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    refine ⟨Subgroup.inv_mem _ g1, Subgroup.inv_mem _ g2, fun x hx => ?_⟩
    have := Submodule.neg_mem _ (g3 _ ((Subgroup.inv_mem _ g2 x).1 hx))
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec, neg_sub] at this
    exact this

variable {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)}

theorem mem_congLev {𝔪 : Ideal (𝓞 E)} {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} : g ∈ congLev hc J Λ 𝔪 ↔
    g ∈ UA hc J ∧ g ∈ Formalism.UG.stabGL (hatL (F := F) Λ) ∧
    ∀ x ∈ hatL (F := F) Λ, g.1 *ᵥ x - x ∈ hatL (F := F) (𝔪 • Λ) := Iff.rfl

theorem congLev_top : congLev hc J Λ ⊤ = UA hc J ⊓ Formalism.UG.stabGL (hatL (F := F) Λ) := by
  ext g
  rw [mem_congLev, Submodule.top_smul]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun x hx => Submodule.sub_mem _ ((h.2 x).1 hx) hx⟩⟩

theorem congLev_mono {𝔪 𝔫 : Ideal (𝓞 E)} (h : 𝔪 ≤ 𝔫) : congLev hc J Λ 𝔪 ≤ congLev hc J Λ 𝔫 := by
  rintro g ⟨g1, g2, g3⟩
  refine ⟨g1, g2, fun x hx => ?_⟩
  refine Submodule.span_mono ?_ (g3 x hx)
  exact Set.image_mono (Submodule.smul_mono_left h)

end Cong

def homLat {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E) where
  carrier := {x | ∀ y ∈ Λ, x *ᵥ y ∈ Λ'}
  zero_mem' := fun y _ => by simp
  add_mem' := fun hx hx' y hy => by rw [add_mulVec]; exact Λ'.add_mem (hx y hy) (hx' y hy)
  smul_mem' := fun r x hx y hy => by rw [smul_mulVec]; exact Λ'.smul_mem r (hx y hy)

def Cos {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) : Type :=
  homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))

def Cos.mk {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (𝔪 : Ideal (𝓞 D.host.E)) (x : homLat Λ Λ') : Cos Λ Λ' 𝔪 := Submodule.Quotient.mk x

instance {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) : Inhabited (Cos Λ Λ' 𝔪) := ⟨Cos.mk 𝔪 0⟩

def hatMx {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) : AddSubgroup (Mx D m n) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, ∃ x ∈ M,
    w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x i j}

def cosSet (e : AE D) {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos Λ Λ' 𝔪) : Set (Mx D m n) :=
  {x | IsHalf e x ∧ ∃ x₀ : homLat Λ Λ', Cos.mk 𝔪 x₀ = κ ∧
    x - e • (x₀ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')}

def cosInd (e : AE D) {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos Λ Λ' 𝔪) : Mx D m n → ℂ :=
  (cosSet e κ).indicator 1

theorem homLat_fg {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (h : Submodule.IsLattice D.host.E Λ) (h' : Λ'.FG) :
    Module.Finite (𝓞 D.host.E) (homLat Λ Λ') := by
  obtain ⟨s, hs⟩ := h.fg
  haveI : Module.Finite (𝓞 D.host.E) Λ' := Module.Finite.iff_fg.2 h'
  let f : homLat Λ Λ' →ₗ[𝓞 D.host.E] (s → Λ') :=
    { toFun := fun x y => ⟨x.1 *ᵥ y.1, x.2 _ (hs ▸ Submodule.subset_span y.2)⟩
      map_add' := fun x x' => funext fun y => Subtype.ext (add_mulVec x.1 x'.1 y.1)
      map_smul' := fun r x => funext fun y => Subtype.ext (smul_mulVec r x.1 y.1) }
  refine Module.Finite.of_injective f ((injective_iff_map_eq_zero f).2 fun x hx => Subtype.ext ?_)
  have h1 : Submodule.span D.host.E (s : Set (Fin n → D.host.E)) = ⊤ := by
    rw [← h.span_eq_top, ← hs, Submodule.span_span_of_tower]
  have h2 : Matrix.mulVecLin x.1 = 0 := LinearMap.ext_on h1 fun y hy => congrArg Subtype.val (congrFun hx ⟨y, hy⟩)
  exact Matrix.toLin'.injective (by rw [Matrix.toLin'_apply', h2]; simp)

theorem finite_cos {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (h : Submodule.IsLattice D.host.E Λ) (h' : Λ'.FG)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (Cos Λ Λ' 𝔪) := by
  haveI := homLat_fg h h'
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  haveI : Module.Finite (𝓞 D.host.E ⧸ 𝔪) (homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 D.host.E) _ _
  exact Module.finite_of_finite (𝓞 D.host.E ⧸ 𝔪) (M := homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ')))

example : antiDiagonalSignGramMatrix 3 (-1 : ℤ) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by decide

example : antiDiagonalSignGramMatrix 4 (-1 : ℤ) = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by decide

abbrev diagSp (D : D7) (n : ℕ) (neg : Fin n → Bool) (p q : ℕ) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral n neg p q

theorem diagSp_gram (n : ℕ) (neg : Fin n → Bool) (p q : ℕ) :
    (diagSp D n neg p q).gram = Matrix.diagonal fun i : Fin n => (Examples₂.sgn (neg i) : D.host.E) :=
  Matrix.ext fun i j => Examples₂.stdSpace_gram_apply _ n neg p q i j

def exDec (D : D7) : HermitianOrthogonalExtensionData (diagSp D 0 ![] 0 0) (diagSp D 3 ![false, true, true] 1 2) 3 (-1) where
  ι := 0
  isom := fun x y => by
    have : x = 0 := funext fun i => i.elim0
    subst this; simp
  a := (!![1, 0, 1 / 2; 1, 0, -1 / 2; 0, 1, 0] : Matrix (Fin 3) (Fin 3) D.host.E)
  gram := by
    rw [diagSp_gram]
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (!![1, 0, 1 / 2; 1, 0, -1 / 2; 0, 1, 0] : Matrix (Fin 3) (Fin 3) D.host.E) *
      (Matrix.diagonal fun i : Fin 3 => (Examples₂.sgn (![false, true, true] i) : D.host.E)) *
      (!![1, 0, 1 / 2; 1, 0, -1 / 2; 0, 1, 0] : Matrix (Fin 3) (Fin 3) D.host.E) = _
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Formalism.UG.cT, transpose_apply, map_apply]
    fin_cases i <;> fin_cases j <;> simp [antiDiagonalSignGramMatrix, Examples₂.sgn, Matrix.diagonal, map_ofNat] <;> norm_num
  perp := Matrix.ext fun i => i.elim0
  rank := rfl

end GlobalTheory.ChiGrid

end
