import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitSumStabLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSplit

section Pure

variable {R : Type} [CommRing R]

theorem mix_mul {l m n : Type} [Fintype m] {b : R} (hb : b * b = b) (A A' : Matrix l m R) (B B' : Matrix m n R) :
    (b • A + (1 - b) • A') * (b • B + (1 - b) • B') = b • (A * B) + (1 - b) • (A' * B') := by
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, hb, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_self {l m : Type} (b : R) (A : Matrix l m R) : b • A + (1 - b) • A = A := by
  rw [← add_smul, add_sub_cancel, one_smul]

def mixGL {n : Type} [Fintype n] [DecidableEq n] {b : R} (hb : b * b = b) (g : GL n R) : GL n R :=
  ⟨b • g.val + (1 - b) • 1, b • (g⁻¹).val + (1 - b) • 1,
    by rw [mix_mul hb, Units.mul_inv, Matrix.mul_one, mix_self],
    by rw [mix_mul hb, Units.inv_mul, Matrix.mul_one, mix_self]⟩

theorem mix_unitary {n : Type} [Fintype n] [DecidableEq n] (σ : R →+* R) {b : R} (hb : b * b = b) (hc : σ b = b)
    (J M : Matrix n n R) (h : (M.map σ)ᵀ * J * M = J) :
    ((b • M + (1 - b) • (1 : Matrix n n R)).map σ)ᵀ * J * (b • M + (1 - b) • 1) = J := by
  have e : ((b • M + (1 - b) • (1 : Matrix n n R)).map σ)ᵀ = b • (M.map σ)ᵀ + (1 - b) • 1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm, map_one]
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  rw [e]
  conv_lhs => rw [← mix_self b J]
  rw [mix_mul hb, mix_mul hb, h, Matrix.one_mul, Matrix.mul_one, mix_self]

theorem mul_det_eq {n : Type} [Fintype n] [DecidableEq n] (a : R) (M N : Matrix n n R)
    (h : ∀ i j, a * M i j = a * N i j) : a * M.det = a * N.det := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R a)
  have hI : ∀ x y, x - y ∈ I ↔ a * x = a * y := fun x y => by
    change a * (x - y) = 0 ↔ _
    rw [mul_sub, sub_eq_zero]
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  exact Ideal.Quotient.eq.2 ((hI _ _).2 (h i j))

theorem det_split {e e' d d₁ d₂ : R} (h3 : e * e' = 0) (k1 : e * d₁ = e * d)
    (k2 : e' * d₂ = e' * d) : (e + e') * d + (1 - (e + e')) = (e * d₁ + (1 - e)) * (e' * d₂ + (1 - e')) := by
  rw [k1, k2]
  linear_combination (-(d - 1) ^ 2) * h3

theorem idempotent_mul_cut_sub_one_entry {b b' m : R} (hb : b * b = b) (hb' : b' * b' = b') (h : b * b' = 0)
    (hm : (b + b') * m = m) : b' * ((1 - b) * m) = (1 - b) * m := by
  have : (1 - b) * m = b' * m := by linear_combination (b - 1) * hm - m * hb - m * h
  rw [this, ← mul_assoc, hb']

theorem keep_inv {n : Type} [Fintype n] [DecidableEq n] (p : (n → R) → Prop) (g : GL n R)
    (h : ∀ y, p y ↔ p (g.val.mulVec y)) (y : n → R) : p y ↔ p ((g⁻¹).val.mulVec y) := by
  rw [h ((g⁻¹).val.mulVec y), Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem idem_laws (σ : R →+* R) (cc : ∀ x, σ (σ x) = x) {e e' : R} (h1 : e * e = e) (h2 : e * σ e = 0)
    (a0 : e' * e' = e') (a1 : e * e' = 0) (a2 : e' * σ e = 0) (a3 : e' * σ e' = 0) :
    (e + σ e) * (e + σ e) = e + σ e ∧ σ (e + σ e) = e + σ e ∧ (1 - (e + σ e)) * (1 - (e + σ e)) = 1 - (e + σ e) ∧
      σ (1 - (e + σ e)) = 1 - (e + σ e) ∧ e * (e + σ e) = e ∧ e' * (1 - (e + σ e)) = e' ∧
      ∀ m, (e + e' + σ (e + e')) * m = m → (e' + σ e') * ((1 - (e + σ e)) * m) = (1 - (e + σ e)) * m := by
  have c0 : σ e' * σ e' = σ e' := by rw [← map_mul, a0]
  have c1 : σ e * σ e' = 0 := by rw [← map_mul, a1, map_zero]
  have c2 : σ e' * e = 0 := by
    have := congrArg σ a2
    rwa [map_mul, cc, map_zero] at this
  have c3 : σ e * σ e = σ e := by rw [← map_mul, h1]
  have hb : (e + σ e) * (e + σ e) = e + σ e := by linear_combination h1 + c3 + 2 * h2
  have hc : σ (e + σ e) = e + σ e := by rw [map_add, cc, add_comm]
  refine ⟨hb, hc, by linear_combination hb, by rw [map_sub, map_one, hc], by linear_combination h1 + h2,
    by linear_combination -a1 - a2, fun m hm => idempotent_mul_cut_sub_one_entry hb (by linear_combination a0 + c0 + 2 * a3)
      (by linear_combination a1 + a2 + c1 + c2) ?_⟩
  rw [map_add] at hm
  rwa [add_add_add_comm]

theorem om_mul_eig {G M : Type} [Monoid G] [AddCommGroup M] [Module ℂ M] (om : G →* Module.End ℂ M) {p p₁ p₂ : G}
    {c c₁ c₂ : Circle} {f : M} (hp : p = p₁ * p₂) (h₁ : om p₁ f = (c₁ : ℂ) • f) (h₂ : om p₂ f = (c₂ : ℂ) • f)
    (hc : c = c₂ * c₁) : om p f = (c : ℂ) • f := by
  rw [hp, hc, map_mul, Module.End.mul_apply, h₂, map_smul, h₁, smul_smul, Circle.coe_mul]

end Pure

variable {D : D7}

open GlobalTheory.AdelicLatMove (mt_mul mt_one)

theorem ext_mt {V : HSp D} {g g' : GA D V} (h : mt V g = mt V g') : g = g' := Subtype.ext (Units.ext h)

def cut (b : AE D) (hb : b * b = b) (hc : cA D b = b) (V : HSp D) (g : GA D V) : GA D V :=
  ⟨mixGL hb (matHom V g), mix_unitary (cA D) hb hc (V.gram.map (incA D)) (mt V g) g.2⟩

variable {b : AE D} (hb : b * b = b) (hc : cA D b = b)

theorem mt_cut (V : HSp D) (g : GA D V) : mt V (cut b hb hc V g) = b • mt V g + (1 - b) • 1 := rfl

theorem cut_inv (V : HSp D) (g : GA D V) : (cut b hb hc V g)⁻¹ = cut b hb hc V g⁻¹ := ext_mt rfl

theorem cut_mul_cut (hb' : (1 - b) * (1 - b) = 1 - b) (hc' : cA D (1 - b) = 1 - b) (V : HSp D) (g : GA D V) :
    cut b hb hc V g * cut (1 - b) hb' hc' V g = g := by
  refine ext_mt ?_
  rw [mt_mul, mt_cut, mt_cut, sub_sub_cancel, add_comm ((1 - b) • _), mix_mul hb, Matrix.mul_one, Matrix.one_mul,
    mix_self]

theorem mt_cut_sub (V : HSp D) (g : GA D V) (i j : Fin V.rank) :
    (mt V (cut b hb hc V g) - 1) i j = b * (mt V g - 1) i j := by
  simp only [mt_cut, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem mul_det_cut (V : HSp D) (g : GA D V) {a : AE D} (ha : a * b = a) :
    a * (mt V (cut b hb hc V g)).det = a * (mt V g).det := by
  refine mul_det_eq a _ _ fun i j => ?_
  simp only [mt_cut, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (mt V g i j - (1 : Matrix _ _ (AE D)) i j) * ha

theorem actO_cut (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T (cut b hb hc S g) (cut b hb hc T h) u = b • actO S T g h u + (1 - b) • u := by
  unfold actO
  rw [cut_inv, mt_cut, mt_cut]
  conv_lhs => rw [← mix_self b u]
  rw [mix_mul hb, mix_mul hb, Matrix.one_mul, Matrix.mul_one]

variable {S T : HSp D}

theorem stable_iff {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} :
    (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) ↔
      (∀ u ∈ Λ, actO S T g h u ∈ Λ) ∧ ∀ u ∈ Λ, actO S T g⁻¹ h⁻¹ u ∈ Λ := by
  refine ⟨fun H => ⟨fun u => (H u).1, fun u hu => (H _).2 ?_⟩, fun H u => ⟨H.1 u, fun hu => ?_⟩⟩
  · rwa [GlobalTheory.AdelicLatMove.actO_actO_inv]
  · have := H.2 _ hu
    rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

theorem stable_cut {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {g : GA D S} {h : GA D T}
    (H : ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔ actO S T g h u ∈ latO S T LS LT fun _ => True) :
    ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔
      actO S T (cut b hb hc S g) (cut b hb hc T h) u ∈ latO S T LS LT fun _ => True := by
  have hb' : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [stable_iff] at H ⊢
  rw [cut_inv, cut_inv]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [actO_cut]
    exact add_mem (GlobalTheory.PlaceModelSum.idem_smul_latO hb (H.1 u hu)) (GlobalTheory.PlaceModelSum.idem_smul_latO hb' hu)
  · rw [actO_cut]
    exact add_mem (GlobalTheory.PlaceModelSum.idem_smul_latO hb (H.2 u hu)) (GlobalTheory.PlaceModelSum.idem_smul_latO hb' hu)

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem stabLat_inv {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {g : GA D V}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ g) : GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ g⁻¹ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat
  rw [MonoidHom.map_inv]
  exact keep_inv (fun y => y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) _ hg

theorem actO_mem_of_stab {g : GA D S} {h : GA D T} (hg : GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat S ΛS g)
    (hh : GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat T ΛT h) (u : WO S T) (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS ΛT a ha _
      ((hg _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      ((hh _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem split_det {e e' : AE D} (he : e * e = e) (he' : e' * e' = e') (h0 : e * e' = 0) (h1 : e * b = e)
    (h2 : e' * (1 - b) = e') (hb' : (1 - b) * (1 - b) = 1 - b) (hc' : cA D (1 - b) = 1 - b) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hx : IsDetAt (e + e') V g x) :
    x = GlobalTheory.VecInv.detAt e he V (cut b hb hc V g) * GlobalTheory.VecInv.detAt e' he' V (cut (1 - b) hb' hc' V g) :=
  Units.ext (hx.trans (det_split h0 (mul_det_cut hb hc V g h1) (mul_det_cut hb' hc' V g h2)))

theorem splitFacO_mul (χS χT : (AE D)ˣ →* Circle) (x x' y y' : (AE D)ˣ) :
    splitFacO χS χT (x * x') (y * y') = splitFacO χS χT x' y' * splitFacO χS χT x y := by
  rw [splitFacO, splitFacO, splitFacO, χS.map_mul, χT.map_mul, mul_inv, mul_mul_mul_comm, mul_comm]

theorem om_latVac_step {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f) {e e' : AE D} (he : IsSplitIdem D e)
    (a0 : e' * e' = e') (a1 : e * e' = 0) (a2 : e' * cA D e = 0) (a3 : e' * cA D e' = 0)
    (ih : ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ latO S T ΛS ΛT fun _ => True) →
      ∀ x y, IsDetAt e' S g x → IsDetAt e' T h y → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f)
    {g : GA D S} {h : GA D T} (hg : SuppAt (e + e') S g) (hh : SuppAt (e + e') T h)
    (hL : ∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ latO S T ΛS ΛT fun _ => True)
    {x y : (AE D)ˣ} (hx : IsDetAt (e + e') S g x) (hy : IsDetAt (e + e') T h y) :
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  obtain ⟨hb, hc, hb', hc', d2, d3, d4⟩ := idem_laws (cA D) GlobalTheory.DualPairCheck.cA_cA he.1 he.2.1 a0 a1 a2 a3
  have s1 : ∀ (V : HSp D) (g : GA D V), SuppAt e V (cut _ hb hc V g) := fun V g i j => by
    rw [mt_cut_sub, ← mul_assoc, hb]
  have s2 : ∀ (V : HSp D) (g : GA D V), SuppAt (e + e') V g → SuppAt e' V (cut _ hb' hc' V g) := fun V g hg i j => by
    rw [mt_cut_sub]
    exact d4 _ (hg i j)
  have r1 := GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he _ _ (s1 S g) (s1 T h)
    (stable_cut hb hc hL) _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) f hf hvac
  have r2 := ih _ _ (s2 S g hg) (s2 T h hh) (stable_cut hb' hc' hL) _ _ (GlobalTheory.VecInv.isDetAt_detAt e' a0 S _)
    (GlobalTheory.VecInv.isDetAt_detAt e' a0 T _)
  have e1 : (g, h) = (cut _ hb hc S g, cut _ hb hc T h) * (cut _ hb' hc' S g, cut _ hb' hc' T h) :=
    Prod.ext (cut_mul_cut hb hc hb' hc' S g).symm (cut_mul_cut hb hc hb' hc' T h).symm
  exact om_mul_eig om e1 r1 r2 ((congrArg₂ (splitFacO χS χT) (split_det hb hc he.1 a0 a1 d2 d3 hb' hc' hx)
    (split_det hb hc he.1 a0 a1 d2 d3 hb' hc' hy)).trans (splitFacO_mul χS χT _ _ _ _))

theorem om_latVac_sum {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f) {ι : Type} (es : ι → AE D) (P : Finset ι) :
    (∀ i ∈ P, IsSplitIdem D (es i)) → (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) →
      (∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0) → ∀ (g : GA D S) (h : GA D T), SuppAt (∑ i ∈ P, es i) S g →
      SuppAt (∑ i ∈ P, es i) T h →
      (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ latO S T ΛS ΛT fun _ => True) →
      ∀ x y, IsDetAt (∑ i ∈ P, es i) S g x → IsDetAt (∑ i ∈ P, es i) T h y →
        om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ _ g h hg hh _ x y hx hy
    rw [Finset.sum_empty] at hg hh hx hy
    have k : ∀ (V : HSp D) (g : GA D V), SuppAt 0 V g → g = 1 := fun V g hg => ext_mt (by
      rw [mt_one, ← sub_eq_zero]
      ext i j
      rw [← hg i j, RingHom.map_zero, add_zero, zero_mul, Matrix.zero_apply])
    have k' : ∀ (V : HSp D) (g : GA D V) (x : (AE D)ˣ), IsDetAt 0 V g x → x = 1 := fun V g x hx =>
      Units.ext (hx.trans (by rw [zero_mul, zero_add, sub_zero, Units.val_one]))
    rw [k S g hg, k T h hh, k' S g x hx, k' T h y hy, Prod.mk_one_one, map_one, splitFacO, map_one, map_one, inv_one,
      mul_one, Circle.coe_one, one_smul, Module.End.one_apply]
  | insert i P hi ih =>
    intro h1 h2 h3 g h hg hh hL x y hx hy
    have m0 := Finset.mem_insert_self i P
    have h1' : ∀ j ∈ P, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ P, ∀ k ∈ P, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have ih' := ih h1' h2' fun j hj k hk => h3 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have a0 : (∑ j ∈ P, es j) * ∑ j ∈ P, es j = ∑ j ∈ P, es j :=
      GlobalTheory.PlaceModelSum.IsOrthSum.idem ⟨ι, P, es, h1', h2', rfl⟩
    have a1 : es i * ∑ j ∈ P, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i m0 j (Finset.mem_insert_of_mem hj) fun h => hi (h ▸ hj)
    have a2 : (∑ j ∈ P, es j) * cA D (es i) = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => h3 j (Finset.mem_insert_of_mem hj) i m0
    have a3 : (∑ j ∈ P, es j) * cA D (∑ j ∈ P, es j) = 0 := by
      rw [map_sum, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk =>
        h3 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    rw [Finset.sum_insert hi] at hg hh hx hy
    exact om_latVac_step hW hS hT hf hvac (h1 i m0) a0 a1 a2 a3 ih' hg hh hL hx hy

theorem exists_orth {e : AE D} (he : GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.IsSplitSum e) :
    GlobalTheory.PlaceModelSum.IsOrthSum e ∧ e * cA D e = 0 := by
  rcases he with he | ⟨P, he⟩
  · exact ⟨⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩,
      he.2.1⟩
  · exact ⟨GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he, he.2⟩

theorem weilSplitFormula : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.WeilSplitFormula D := by
  intro D ψ θ S T χS χT om hW sS sT ΛS ΛT hS hT f₀ hf e he
  obtain ⟨ho, hec⟩ := exists_orth he
  have key : ∀ a, GlobalTheory.PlaceModelSum.IsOrthSum a → ∀ Tm,
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
      GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.LinearLaw S T χS χT om ΛS ΛT e a Tm := by
    intro a ha Tm hTm g h hg hh sg sh x y hx hy Φ hΦ
    have hL := stable_iff.2 ⟨actO_mem_of_stab sg sh, actO_mem_of_stab (stabLat_inv sg) (stabLat_inv sh)⟩
    obtain ⟨ι, P, es, h1, h2, rfl⟩ := ho
    have h3 : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 := fun i hi j hj => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hj, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    have h0 := om_latVac_sum hW hS hT hf.2.theta hf.2.lat es P h1 h2 h3 g h hg hh hL x y hx hy
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.factor_eq]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt_eq_actO]
    exact GlobalTheory.SchrodSubst.om_placeModel D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha.idem ha.infPart_eq hf.2.theta hTm
      g h _ hL h0 Φ hΦ
  exact ⟨key e ho, key _ ho.conj⟩

end GlobalTheory.WeilSplit

end
