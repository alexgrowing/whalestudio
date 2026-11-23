import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupAlgebraSingleOneMemOfSpan
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart

section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb

theorem isUnit_of_map {c : A} (h : IsUnit (f c)) : IsUnit c := by
  obtain ⟨t, ht⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := hb.2 t
  have e : AddMonoidAlgebra.single (0 : X) c * b = 1 := by
    apply hb.1
    rw [map_mul, map_one, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one, ht]
  have e' := congrArg (AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A)
    (fun _ _ => Commute.all _ _)) e
  rw [map_mul, map_one, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one] at e'
  exact IsUnit.of_mul_eq_one _ e'

theorem eq_mono {s : R} {α : X} (h : ∀ χ, χ ≠ α → cf hb χ s = 0) :
    s = f (cf hb α s) * m (Multiplicative.ofAdd α) := by
  refine cf_ext hb fun χ => ?_
  rw [cf_mono]
  split_ifs with e
  · rw [e]
  · exact h χ fun e' => e e'.symm

theorem subring_eq_top {I : Type} (e : Module.Basis I ℤ X) (S : Subring R) (h0 : ∀ a, f a ∈ S)
    (h : ∀ i, Ideal.span {a : A | f a * m (Multiplicative.ofAdd (e i)) ∈ S} = ⊤ ∧
      Ideal.span {a : A | f a * m (Multiplicative.ofAdd (-e i)) ∈ S} = ⊤) : S = ⊤ := by
  have := GlobalTheory.groupAlgebra_subring_eq_top A X I e
    (S.comap (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (fun a => by
      rw [Subring.mem_comap, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one]
      exact h0 a)
    (fun i => by
      simpa only [Subring.mem_comap, AddMonoidAlgebra.liftNCRingHom_single] using h i)
  rw [eq_top_iff]
  intro s _
  obtain ⟨b, rfl⟩ := hb.2 s
  exact Subring.mem_comap.1 (this.ge (Subring.mem_top b))

end Alg

variable {k : Type} [Field k] (Φ : FibPre k)

theorem pure_res {α : Φ.E.X} {φ : (Φ.H 1).Sec} (hφ : Φ.Pure α φ) (l : Φ.N₀.ι) {W : Φ.E.B.left.Opens}
    (h : W ≤ Φ.N₀.U l) : ∃ c : Γ(Φ.E.B.left, W), resG _ (Φ.D.q.left.preimage_mono h) (φ.f l) =
      (Φ.D.q.left.app W).hom c * mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) := by
  have e := eq_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (s := φ.f l) (α := α)
    (fun χ hχ => by
      by_contra hne
      exact hχ (hφ ⟨l, hne⟩))
  obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) (h.trans (Φ.le l)) h α
  refine ⟨resG _ h (Φ.wt φ α l) * c, (congrArg (resG _ (Φ.D.q.left.preimage_mono h)) e).trans
    ((map_mul (resG _ (Φ.D.q.left.preimage_mono h)) _ _).trans ?_)⟩
  rw [hc, rapp, map_mul, _root_.mul_assoc]
  rfl

theorem ratio_res {α : Φ.E.X} {φ φ₀ : (Φ.H 1).Sec} (hφ : Φ.Pure α φ) (hφ₀ : Φ.Pure 0 φ₀)
    {V W : Φ.E.B.left.Opens} (hV : Φ.D.q.left ⁻¹ᵁ V ≤ Out.nonzeroLocus φ₀) (hW : IsAffineOpen W)
    (hWV : W ≤ V) (l : Φ.N₀.ι) (h : W ≤ Φ.N₀.U l) {r : Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ V)}
    (hr : IsRatio φ φ₀ _ r) : ∃ a : Γ(Φ.E.B.left, W),
      resG _ (Φ.D.q.left.preimage_mono hWV) r =
        (Φ.D.q.left.app W).hom a * mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) ∧
      Φ.D.q.left ⁻¹ᵁ W ⊓ Out.nonzeroLocus φ ≤ Φ.D.q.left ⁻¹ᵁ Φ.E.B.left.basicOpen a := by
  obtain ⟨c, hc⟩ := pure_res Φ hφ l h
  obtain ⟨c₀, hc₀⟩ := pure_res Φ hφ₀ l h
  rw [ofAdd_zero, map_one, _root_.mul_one] at hc₀
  have hu := GlobalTheory.SecRatio.isUnit_res φ₀ l ((Φ.D.q.left.preimage_mono hWV).trans hV)
    (Φ.D.q.left.preimage_mono h)
  have hu' : IsUnit ((Φ.D.q.left.app W).hom c₀) := hc₀ ▸ hu
  obtain ⟨u, rfl⟩ := isUnit_of_map (Φ.D.coord (Φ.ch l) W hW (h.trans (Φ.le l))) hu'
  have hle : Φ.D.q.left ⁻¹ᵁ W ≤ Φ.D.q.left ⁻¹ᵁ V ⊓ (Φ.H 1).U l :=
    le_inf (Φ.D.q.left.preimage_mono hWV) (Φ.D.q.left.preimage_mono h)
  have e := congrArg (resG _ hle) (hr l)
  rw [map_mul, rr, rr, rr] at e
  have e' : (Φ.D.q.left.app W).hom c * mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) =
      resG _ (Φ.D.q.left.preimage_mono hWV) r * (Φ.D.q.left.app W).hom u :=
    hc.symm.trans (e.trans (congrArg _ hc₀))
  refine ⟨c * ↑u⁻¹, ?_, ?_⟩
  · rw [map_mul, mul_right_comm, e', _root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.mul_one]
  · have hv := GlobalTheory.SecRatio.isUnit_res φ l
      (inf_le_right : Φ.D.q.left ⁻¹ᵁ W ⊓ Out.nonzeroLocus φ ≤ _)
      (inf_le_left.trans (Φ.D.q.left.preimage_mono h))
    have e₂ := congrArg (resG _ (inf_le_left : Φ.D.q.left ⁻¹ᵁ W ⊓ Out.nonzeroLocus φ ≤ _)) hc
    have e₄ := (rr _ _ _).symm.trans (e₂.trans (map_mul _ _ _))
    have hv' := isUnit_of_mul_isUnit_left (e₄ ▸ hv)
    have e₃ := Φ.G.left.basicOpen_of_isUnit hv'
    rw [Scheme.basicOpen_mul, Φ.E.B.left.basicOpen_of_isUnit (Units.isUnit _),
      inf_eq_left.2 (Φ.E.B.left.basicOpen_le c), Scheme.preimage_basicOpen, ← e₃]
    erw [Scheme.basicOpen_res]
    exact inf_le_right

theorem span_eq_top [IsAlgClosed k] {α : Φ.E.X} {φ₀ : (Φ.H 1).Sec} (hφ₀ : Φ.Pure 0 φ₀)
    {V W : Φ.E.B.left.Opens} (hV : Φ.D.q.left ⁻¹ᵁ V ≤ Out.nonzeroLocus φ₀) (hW : IsAffineOpen W)
    (hWV : W ≤ V) (l : Φ.N₀.ι) (h : W ≤ Φ.N₀.U l)
    (hx : ∀ x : Φ.Pt, ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)
    (S : Subring Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ W))
    (hS : ∀ (φ : (Φ.H 1).Sec) r, Φ.Pure α φ → IsRatio φ φ₀ (Φ.D.q.left ⁻¹ᵁ V) r →
      resG _ (Φ.D.q.left.preimage_mono hWV) r ∈ S) :
    Ideal.span {a : Γ(Φ.E.B.left, W) | (Φ.D.q.left.app W).hom a *
      mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) ∈ S} = ⊤ := by
  rw [← hW.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun a => Φ.E.B.left.basicOpen_le _) ?_
  set U : Φ.E.B.left.Opens := ⨆ a : {a : Γ(Φ.E.B.left, W) | (Φ.D.q.left.app W).hom a *
      mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) ∈ S},
      Φ.E.B.left.basicOpen (a : Γ(Φ.E.B.left, W)) with hU
  by_contra hn
  have := Φ.E.isAbelian.proper
  have : JacobsonSpace Φ.E.B.left := LocallyOfFiniteType.jacobsonSpace Φ.E.B.hom
  have hne : ((W : Set Φ.E.B.left) ∩ (U : Set Φ.E.B.left)ᶜ).Nonempty := by
    obtain ⟨y, hy, hy'⟩ := Set.not_subset.1 hn
    exact ⟨y, hy, hy'⟩
  obtain ⟨b, ⟨hbW, hbU⟩, hb⟩ := nonempty_inter_closedPoints hne
    (W.isOpen.isLocallyClosed.inter U.isOpen.isClosed_compl.isLocallyClosed)
  obtain ⟨x, hxb⟩ := (GlobalTheory.TorsLift.points_lift k Φ.E Φ.G Φ.D 1 le_rfl).1
    (Over.homMk (pointOfClosedPoint Φ.E.B.hom b hb) (pointOfClosedPoint_comp Φ.E.B.hom b hb))
  obtain ⟨φ, hφ, hxφ⟩ := hx x
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio (Φ.H_isLB 1) φ φ₀ _ hV
  obtain ⟨a, ha, ha'⟩ := ratio_res Φ hφ hφ₀ hV hW hWV l h hr
  let p : Sp k := IsLocalRing.closedPoint k
  have hq : Φ.D.q.left (x.left p) = b :=
    (Scheme.Hom.comp_apply x.left Φ.D.q.left p).symm.trans
      ((congrArg (fun z => z.left p) hxb).trans (pointOfClosedPoint_apply Φ.E.B.hom b hb p))
  have h1 : x.left p ∈ Φ.D.q.left ⁻¹ᵁ Φ.E.B.left.basicOpen a :=
    ha' ⟨show Φ.D.q.left (x.left p) ∈ W from hq ▸ hbW, hxφ (show p ∈ ⊤ from trivial)⟩
  have h2 : b ∈ Φ.E.B.left.basicOpen a := hq ▸ h1
  exact hbU (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, show _ ∈ S from ha ▸ hS φ r hφ hr⟩, h2⟩)

def satur {C C' : Type} [CommRing C] [CommRing C'] (σ : C →+* C') (F : C) (R : Subring C) (hF : F ∈ R) :
    Subring C' where
  carrier := {c | ∃ n : ℕ, ∃ r ∈ R, σ F ^ n * c = σ r}
  zero_mem' := ⟨0, 0, R.zero_mem, by simp⟩
  one_mem' := ⟨0, 1, R.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨n, r, hr, e⟩ ⟨m, s, hs, e'⟩
    refine ⟨n + m, F ^ m * r + F ^ n * s,
      R.add_mem (R.mul_mem (R.pow_mem hF _) hr) (R.mul_mem (R.pow_mem hF _) hs), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
    ring
  mul_mem' := by
    rintro a b ⟨n, r, hr, e⟩ ⟨m, s, hs, e'⟩
    refine ⟨n + m, r * s, R.mul_mem hr hs, ?_⟩
    rw [map_mul, ← e, ← e']
    ring
  neg_mem' := by
    rintro a ⟨n, r, hr, e⟩
    exact ⟨n, -r, R.neg_mem hr, by rw [map_neg, ← e, mul_neg]⟩

theorem ratios_generate : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (I : Type) (e : Module.Basis I ℤ Φ.E.X) (φ₀ : (Φ.H 1).Sec) (V : Φ.E.B.left.Opens), IsAffineOpen V → Φ.Pure 0 φ₀ → Φ.D.q.left ⁻¹ᵁ V ≤ Out.nonzeroLocus φ₀ → (∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ R : Subring Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ V), (∀ a, (Φ.D.q.left.app V).hom a ∈ R) → (∀ i (φ : (Φ.H 1).Sec) r, (Φ.Pure (e i) φ ∨ Φ.Pure (-e i) φ) → IsRatio φ φ₀ _ r → r ∈ R) → R = ⊤) := by
  intro k _ _ Φ I e φ₀ V hV hφ₀ hVφ hx R h0 hR
  rw [eq_top_iff]
  intro s _
  let J : Ideal Γ(Φ.E.B.left, V) :=
    { carrier := {a | (Φ.D.q.left.app V).hom a * s ∈ R}
      zero_mem' := by
        show _ ∈ R
        rw [map_zero, zero_mul]; exact R.zero_mem
      add_mem' := fun {a b} ha hb => by
        show _ ∈ R
        rw [map_add, add_mul]; exact R.add_mem ha hb
      smul_mem' := fun c a ha => by
        show _ ∈ R
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]; exact R.mul_mem (h0 c) ha }
  suffices hJ : J = ⊤ by
    have h1 : (Φ.D.q.left.app V).hom 1 * s ∈ R := (hJ.ge (Submodule.mem_top : (1 : Γ(Φ.E.B.left, V)) ∈ ⊤) :)
    rwa [map_one, _root_.one_mul] at h1
  rw [← Ideal.span_eq J, ← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun a => Φ.E.B.left.basicOpen_le _) fun b hb => ?_
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show b ∈ ⊤ from trivial))
  obtain ⟨f, hfl, hbf⟩ := hV.exists_basicOpen_le ⟨b, hl⟩ hb
  have hW := hV.basicOpen f
  have hWV := Φ.E.B.left.basicOpen_le f
  let σ := resG _ (Φ.D.q.left.preimage_mono hWV)
  let F := (Φ.D.q.left.app V).hom f
  have hS : satur σ F R (h0 f) = ⊤ := by
    refine subring_eq_top (Φ.D.coord (Φ.ch l) _ hW (hfl.trans (Φ.le l))) e _ (fun a => ?_) fun i =>
      ⟨span_eq_top Φ hφ₀ hVφ hW hWV l hfl (hx _) _ fun φ r hφ hr =>
        ⟨0, r, hR i φ r (Or.inl hφ) hr, by rw [pow_zero, _root_.one_mul]⟩,
      span_eq_top Φ hφ₀ hVφ hW hWV l hfl (hx _) _ fun φ r hφ hr =>
        ⟨0, r, hR i φ r (Or.inr hφ) hr, by rw [pow_zero, _root_.one_mul]⟩⟩
    have := hV.isLocalization_basicOpen f
    obtain ⟨⟨a', _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f) a
    refine ⟨n, _, h0 a', ?_⟩
    have ha' : a * resG _ hWV (f ^ n) = resG _ hWV a' := ha
    change resG _ _ _ ^ n * _ = resG _ _ _
    rw [rapp _ hWV, rapp _ hWV, ← ha', map_mul, map_pow, map_pow, mul_comm]
  obtain ⟨n, r, hr, hnr⟩ : σ s ∈ satur σ F R (h0 f) := hS.ge (Subring.mem_top _)
  have := Φ.D.q_affine
  have hz : resG _ (Φ.G.left.basicOpen_le F) (F ^ n * s - r) = 0 := by
    have hle : Φ.G.left.basicOpen F ≤ Φ.D.q.left ⁻¹ᵁ Φ.E.B.left.basicOpen f :=
      (Scheme.preimage_basicOpen _ _).ge
    have : σ (F ^ n * s - r) = 0 := by rw [map_sub, map_mul, map_pow, hnr, sub_self]
    rw [← rr (Φ.D.q.left.preimage_mono hWV) hle]
    exact (congrArg (resG _ hle) this).trans (map_zero _)
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Φ.G.left
    (hV.preimage Φ.D.q.left) (F ^ n * s - r) F hz
  have hmem : f ^ (m + n + 1) ∈ J := by
    show _ ∈ R
    have : F ^ (m + n + 1) * s = F ^ (m + 1) * r := by linear_combination F * hm
    rw [map_pow, this]
    exact R.mul_mem (R.pow_mem (h0 f) _) hr
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, hmem⟩, ?_⟩
  rw [Scheme.basicOpen_pow _ _ (Nat.succ_pos _)]
  exact hbf

end GlobalTheory.ZH.WtGen
end
