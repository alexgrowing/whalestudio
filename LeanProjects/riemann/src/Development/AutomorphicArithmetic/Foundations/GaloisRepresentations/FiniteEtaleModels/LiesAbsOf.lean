import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem desc_sq {I B : Type} {W Z Y Y' : Scheme.{0}} (cls : I → B) (f : I → (W ⟶ Z)) (kc : I → (W ⟶ Y')) (π : Z ⟶ Y) (t : B → (Y' ⟶ Y))
    (h : ∀ c, f c ≫ π = kc c ≫ t (cls c)) :
    Sigma.desc f ≫ π = (Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c)) ≫ Sigma.desc t := by
  refine Limits.Sigma.hom_ext _ _ fun c => ?_
  simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Category.assoc, h]

set_option maxHeartbeats 200000 in
theorem liesAbs_of (hP : LPts) (hC : LCount) (hI : LIdx) (hS : SigmaFEt) : LiesAbs := by
  intro p _ D G L E _ _ gb k T N J A _ g θ O _ _ C j K₀ K₁ Y' π' s d hK hN hq0 hq1 hc hs hcos ht
  have trc : ∀ {i i' : T.X.ι} (x y : G.GAf) (e : x = y) (a : x ∈ T.X.Δ)
      (b : ∀ u ∈ T.X.K i, x * u * x⁻¹ ∈ T.X.K i') (a' : y ∈ T.X.Δ)
      (b' : ∀ u ∈ T.X.K i, y * u * y⁻¹ ∈ T.X.K i'), T.X.tr i i' x a b = T.X.tr i i' y a' b' := by
    intro i i' x y e a b a' b'
    subst e
    rfl
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hMpos : 0 < ((g j).M : ℕ) := by
    have := (g j).M.2.1
    omega
  have hNK : (L.KN (N : ℕ)).relIndex (g j).K ≠ 0 := by
    have h1 := hI p D G L (N : ℕ) hNpos
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h1
    exact left_ne_zero_of_mul h1
  have hK0 : K₀.relIndex (g j).K ≠ 0 := fun h0 => hNK (Subgroup.relIndex_eq_zero_of_le_left hN h0)
  haveI : Finite (g j).I := by
    haveI : ((L.KN (N : ℕ)).subgroupOf (g j).K).FiniteIndex := ⟨hNK⟩
    show Finite (↥(g j).K ⧸ (L.KN (N : ℕ)).subgroupOf (g j).K)
    infer_instance
  haveI : Finite (↥(g j).K ⧸ K₀.subgroupOf (g j).K) := by
    haveI : (K₀.subgroupOf (g j).K).FiniteIndex := ⟨hK0⟩
    infer_instance
  have hm0 : (T.X.K (T.lev (g j).M)).relIndex ((g j).K ⊓ K₁) ≠ 0 := by
    have hle1 : T.X.K (T.lev (g j).M) ≤ (g j).K ⊓ K₁ := by
      refine le_inf ?_ hq1.le
      rw [T.K_eq]
      exact (KN_anti (g j).dvd).trans (g j).le
    have hle2 : (g j).K ⊓ K₁ ≤ L.KN 1 := inf_le_left.trans (g j).le_one
    have h1 := hI p D G L ((g j).M : ℕ) hMpos
    rw [← T.K_eq, ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2] at h1
    exact left_ne_zero_of_mul h1
  have a1 : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have b1 : ∀ u ∈ T.X.K (T.lev (g j).M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := by
    intro u hu
    rw [T.K_eq] at hu ⊢
    simpa using KN_anti (g j).dvd hu
  have aH : ∀ x ∈ (g j).K, (g j).h * x ∈ T.X.Δ := fun x hx =>
    (T.Δ_eq _).2 ((g j).int.mul (integ_of_mem ((g j).le_one hx)))
  have bH : ∀ x ∈ (g j).K, ∀ u ∈ T.X.K (T.lev (g j).M),
      (g j).h * x * u * ((g j).h * x)⁻¹ ∈ T.X.K (T.lev N) := by
    intro x hx u hu
    rw [T.K_eq] at hu ⊢
    exact (g j).adm x hx u hu
  let cls : (g j).I → ↥(g j).K ⧸ K₀.subgroupOf (g j).K := fun c => QuotientGroup.mk (Quotient.out c)
  let u : (g j).I → G.GAf := fun c => (↑(Quotient.out (cls c)) : G.GAf)⁻¹ * ↑(Quotient.out c)
  have hmem : ∀ c, u c ∈ K₀ := by
    intro c
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (cls c))
    simpa [Subgroup.mem_subgroupOf] using h
  let kc : (g j).I → (T.X.Z (T.lev (g j).M) ⟶ Y') := fun c =>
    T.X.tr _ _ (u c) (hq0.adm _ (hmem c)).1 (hq0.adm _ (hmem c)).2 ≫ π'
  choose tb0 htb1 htb2 using ht
  let tb : (↥(g j).K ⧸ K₀.subgroupOf (g j).K) → (Y' ⟶ C.Y) := fun b => tb0 _ (Quotient.out b).2
  have hsq' : ∀ c, T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1 ≫ C.π = kc c ≫ s := by
    intro c
    rw [hc]
    simp only [kc, Category.assoc]
    exact (hq0.inv _ (hmem c) _ _).symm
  have hsq : (T.tower N g).s j ≫ C.π =
      (Limits.Sigma.desc fun c => kc c ≫ Limits.Sigma.ι (fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y') (cls c)) ≫
        Limits.Sigma.desc fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => s :=
    desc_sq cls (fun _ => T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1) kc C.π (fun _ => s) hsq'
  refine ⟨∐ fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y', Limits.Sigma.desc fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => s, Limits.Sigma.desc tb,
    Nat.card (↥(g j).K ⧸ K₀.subgroupOf (g j).K) * d, (T.X.K (T.lev (g j).M)).relIndex ((g j).K ⊓ K₁),
    hS C.Y Y' s d _ hs, ?_, Nat.pos_of_ne_zero hm0, _, hsq, ?_, ?_⟩
  · refine Limits.Sigma.hom_ext _ _ fun b => ?_
    simp only [Limits.Sigma.ι_desc_assoc, tb, htb1]
  · refine Limits.Sigma.hom_ext _ _ fun c => ?_
    show Limits.Sigma.ι _ c ≫ (Limits.Sigma.desc fun c => kc c ≫ Limits.Sigma.ι (fun _ : ↥(g j).K ⧸ K₀.subgroupOf (g j).K => Y') (cls c)) ≫ Limits.Sigma.desc tb =
      Limits.Sigma.ι _ c ≫ (Limits.Sigma.desc fun c : (g j).I => T.X.tr (T.lev (g j).M) (T.lev N) ((g j).h * ↑(Quotient.out c)) (aH _ (Quotient.out c).2) (bH _ (Quotient.out c).2)) ≫ C.π
    rw [Limits.Sigma.ι_desc_assoc, Category.assoc, Limits.Sigma.ι_desc]
    erw [Limits.Sigma.ι_desc_assoc]
    have e : (g j).h * ↑(Quotient.out (cls c)) * u c = (g j).h * ↑(Quotient.out c) := by
      show (g j).h * ↑(Quotient.out (cls c)) * ((↑(Quotient.out (cls c)) : G.GAf)⁻¹ * ↑(Quotient.out c)) = _
      rw [_root_.mul_assoc, _root_.mul_inv_cancel_left]
    have key := T.X.tr_mul (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (u c) ((g j).h * ↑(Quotient.out (cls c)))
      (hq0.adm _ (hmem c)).1 (hq0.adm _ (hmem c)).2 (aH _ (Quotient.out (cls c)).2) (bH _ (Quotient.out (cls c)).2)
      (by rw [e]; exact aH _ (Quotient.out c).2) (by rw [e]; exact bH _ (Quotient.out c).2)
    show T.X.tr _ _ (u c) _ _ ≫ π' ≫ tb (cls c) = T.X.tr _ _ ((g j).h * ↑(Quotient.out c)) _ _ ≫ C.π
    rw [show tb (cls c) = tb0 _ (Quotient.out (cls c)).2 from rfl, htb2 _ _ (aH _ (Quotient.out (cls c)).2) (bH _ (Quotient.out (cls c)).2)]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.π) key).trans (congrArg (· ≫ C.π) (trc _ _ e _ _ _ _)))
  · refine hC (g j).I _ _ _ C.Y Y' cls (T.X.tr (T.lev (g j).M) (T.lev N) 1 a1 b1) kc C.π s _
      (T.X.fin _ _ a1 b1) (T.X.etale _ _ a1 b1) hs.1 hs.2.1 ?_ hsq
    intro Ω _ _ z b y' hy
    have hcount := hP E G.GAf T.X O (g j).K K₀ K₁ (L.KN (N : ℕ)) (T.lev (g j).M) (T.lev N) C.Y Y' C.p C.π π' s a1 b1
      (T.K_eq N) (g j).le hN hK C.ov hq0 hq1 (hc a1 b1) hcos (↑(Quotient.out b)) (Quotient.out b).2 Ω z y' hy
    rw [← hcount]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun cx => ?_)
    constructor
    · rintro ⟨h1, rfl, h3⟩
      exact ⟨h1, hmem cx.1, fun a' b' => h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hcl : cls cx.1 = b := by
        rw [← QuotientGroup.out_eq' b]
        refine (QuotientGroup.eq.2 ?_).symm
        simpa [Subgroup.mem_subgroupOf] using h2
      subst hcl
      exact ⟨h1, rfl, h3 _ _⟩

end UpperTheory.Gal.FiniteEtaleModels
