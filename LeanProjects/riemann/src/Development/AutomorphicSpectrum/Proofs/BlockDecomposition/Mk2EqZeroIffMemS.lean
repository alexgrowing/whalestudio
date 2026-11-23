import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZigzagCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegOneSmulCancel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

section SQ

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def vl (T : D) : (sq a b).obj T →+ A.obj T ⧸ b.S T := (sqM a b T).subtype.toAddMonoidHom

def mk2 (T : D) : (CH.modF A).obj T →+ A.obj T ⧸ b.S T := (Ideal.Quotient.mk (b.S T)).toAddMonoidHom

def gC {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) : CH.Cn (sq a b) q := fun s => sqMk a b (x s) (hx s)

variable {a b}

theorem mk2_eq_zero_iff_mem_S {T : D} (x : (CH.modF A).obj T) : mk2 b T x = 0 ↔ x ∈ b.S T := Ideal.Quotient.eq_zero_iff_mem

theorem map_val {T T' : D} (φ : T ⟶ T') (y : (sq a b).obj T) (x : (CH.modF A).obj T) (h : vl a b T y = mk2 b T x) :
    vl a b T' (((sq a b).map φ).hom y) = mk2 b T' (((CH.modF A).map φ).hom x) := by
  obtain ⟨y, hy⟩ := y
  have h' : y = mk2 b T x := h
  subst h'
  rfl

theorem d_val {q : ℕ} (f : CH.Cn (sq a b) q) (x : CH.Cn (CH.modF A) q)
    (h : ∀ s, vl a b _ (f s) = mk2 b _ (x s)) (s : ComposableArrows D (q + 1)) :
    vl a b _ (CH.d _ q f s) = mk2 b _ (CH.d _ q x s) := by
  change vl a b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (GlobalTheory.CatH.toLast i s)).hom (f (GlobalTheory.CatH.face i s))) =
    mk2 b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((CH.modF A).map (GlobalTheory.CatH.toLast i s)).hom (x (GlobalTheory.CatH.face i s)))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, map_val _ _ _ (h _)]

theorem lift_C {q : ℕ} (f : CH.Cn (sq a b) q) : ∃ x : CH.Cn (CH.modF A) q, (∀ s, x s ∈ a.S _) ∧
    ∀ s, vl a b _ (f s) = mk2 b _ (x s) := by
  have h : ∀ s, ∃ y : (CH.modF A).obj (s.obj (Fin.last q)), y ∈ a.S _ ∧ vl a b _ (f s) = mk2 b _ y := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, e.symm⟩
  choose x hx hx' using h
  exact ⟨x, hx, hx'⟩

theorem vl_inj {T : D} {y y' : (sq a b).obj T} (h : vl a b T y = vl a b T y') : y = y' := Subtype.ext h

theorem gC_d {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ q x s ∈ b.S _) :
    CH.d _ q (gC a b x hx) = 0 := by
  funext s
  refine vl_inj ?_
  rw [d_val _ x (fun _ => rfl) s, (mk2_eq_zero_iff_mem_S _).2 (hd s)]
  exact (map_zero (vl a b _)).symm

theorem ex_zero (hH : Subsingleton (CH.H (sq a b) 0)) (x : CH.Cn (CH.modF A) 0) (hx : ∀ s, x s ∈ a.S _)
    (hd : ∀ s, CH.d _ 0 x s ∈ b.S _) (s) : x s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  have h2 : gC a b x hx = 0 := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) 0).2.1 _ h0).1 h1
  have h3 : vl a b _ (gC a b x hx s) = 0 := by rw [h2]; exact map_zero (vl a b _)
  exact (mk2_eq_zero_iff_mem_S _).1 h3

theorem ex_succ {q : ℕ} (hH : Subsingleton (CH.H (sq a b) (q + 1))) (x : CH.Cn (CH.modF A) (q + 1))
    (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ (q + 1) x s ∈ b.S _) :
    ∃ v : CH.Cn (CH.modF A) q, (∀ s, v s ∈ a.S _) ∧ ∀ s, (x - CH.d _ q v) s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) (q + 1)).2.1 _ h0).1 h1
  obtain ⟨v, hv, hv'⟩ := lift_C u
  refine ⟨v, hv, fun s => ?_⟩
  have h3 := d_val u v hv' s
  have h4 : vl a b _ (CH.d _ q u s) = mk2 b _ (x s) :=
    congrArg (fun y : CH.Cn (sq a b) (q + 1) => vl a b _ (y s)) hu
  rw [h4] at h3
  refine (mk2_eq_zero_iff_mem_S _).1 ?_
  change mk2 b _ (x s - CH.d _ q v s) = 0
  rw [map_sub, h3, sub_self]

theorem cls_sub_sum {K : Cx.{1} R} {m : ℕ} {ι : Type} [Fintype ι] (g : K.X m) (hg : K.d m g = 0) (Y : ι → K.X m)
    (hY : ∀ k, K.d m (Y k) = 0) (h : K.d m (g - ∑ k, Y k) = 0) :
    K.cls g hg - ∑ k, K.cls (Y k) (hY k) = K.cls (g - ∑ k, Y k) h := by
  have e : (⟨g - ∑ k, Y k, h⟩ : K.Z m) = ⟨g, hg⟩ - ∑ k, (⟨Y k, hY k⟩ : K.Z m) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, Submodule.coe_sum]
  change _ = Submodule.mkQ _ (⟨g - ∑ k, Y k, h⟩ : K.Z m)
  rw [e, map_sub, map_sum]
  rfl

theorem rep_fin {m : ℕ} {ι : Type} [Fintype ι] {Cl E : CH.Cn (CH.modF A) m} {c : CH.H (sq a b) m} (hc : Rep a b Cl c)
    (Y : ι → CH.Cn (sq a b) m) (y : ι → CH.Cn (CH.modF A) m) (hY : ∀ k, CH.d _ m (Y k) = 0)
    (hy : ∀ k s, vl a b _ (Y k s) = mk2 b _ (y k s)) (hE : Cl - ∑ k, y k = E) :
    Rep a b E (c - ∑ k, (CH.cx (sq a b)).cls (Y k) (hY k)) := by
  obtain ⟨g, hg, rfl, hgs⟩ := hc
  have h : CH.d _ m (g - ∑ k, Y k) = 0 := by
    rw [map_sub, map_sum, hg]
    simp [hY]
  refine ⟨g - ∑ k, Y k, h, cls_sub_sum (K := CH.cx (sq a b)) g hg Y hY h, fun s => ?_⟩
  subst hE
  change vl a b _ (g s - (∑ k, Y k) s) = mk2 b _ (Cl s - (∑ k, y k) s)
  rw [Finset.sum_apply, Finset.sum_apply, map_sub, map_sub, map_sum, map_sum]
  exact congrArg₂ (· - ·) (hgs s) (Finset.sum_congr rfl fun k _ => hy k s)

end SQ

end GlobalTheory.CompanionTheory.ConeZig
