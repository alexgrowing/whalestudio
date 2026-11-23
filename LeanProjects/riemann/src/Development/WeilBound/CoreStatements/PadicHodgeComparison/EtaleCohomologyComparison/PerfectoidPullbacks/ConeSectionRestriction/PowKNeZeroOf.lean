import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.OneKNeZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.WchCover
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RepDlogLifts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechRel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeHyp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GrNegVan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.JacSpanLe
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLiftStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocVan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoordsStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem d_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) j) :
    CH.d _ j (resB A h b) = resB A h (CH.d _ j b) :=
  (CH.Mor.restrict (CH.modF (U.ι ⋙ A)) (ObjectProperty.ιOfLE h)).d_pullC j b

theorem dpow_mem_pdP' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have := dpow_mem_pdP' δ 1 hx
  rwa [δ.dpow_one hx] at this

theorem plogK_mem' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

theorem g_rel {K : Type} [Field K] {X : Scheme.{0}} {N n e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (V W : X.Opens) (hVW : V ≤ W)
    (hW : ∀ b, W ≤ uy i y b) (t : Fin (n + 1) → Γ(X, V)ˣ)
    (ht : ∀ k, (t k : Γ(X, V)) = (i.appLE _ V (hVW.trans (hW 0))).hom (yQ y hy k.succ 0)) (k : Fin (n + 1)) :
    rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) =
      if h : (k : ℕ) = 0 then (((t 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (t ⟨k - 1, by omega⟩ : Γ(X, V)) * (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  have hVb : ∀ b : Fin (n + 2), V ≤ uy i y b := fun b => hVW.trans (hW b)
  set A : Fin (n + 2) → Fin (n + 2) → Γ(X, V) := fun a b =>
    (i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y b)) V (hVb b)).hom (yQ y hy a b)
    with hAdef
  have hA : ∀ a b c : Fin (n + 2), A a b * A b c = A a c := fun a b c =>
    (yQ_mul i y hy a b c V (hVb a) (hVb b) (hVb c)).1
  have hA1 : ∀ a, A a a = 1 := fun a => (yQ_mul i y hy a a a V (hVb a) (hVb a) (hVb a)).2
  have htA : ∀ k : Fin (n + 1), ((t k : Γ(X, V)ˣ) : Γ(X, V)) = A k.succ 0 := fun k => ht k
  have hinv : ∀ k : Fin (n + 1), A 0 k.succ = (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := fun k =>
    Units.eq_inv_of_mul_eq_one_left (by rw [htA, hA, hA1])
  have e0 : rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) = A k.castSucc k.succ :=
    rs_appLE i _ hVW (hW k.succ) (yQ y hy k.castSucc k.succ)
  rw [e0]
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    rw [dif_pos hk]
    exact hinv 0
  · rw [dif_neg hk]
    have e1 : (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)).succ = k.castSucc := Fin.ext (by simp; omega)
    rw [htA, e1, ← hinv k, hA]

set_option maxHeartbeats 800000 in
theorem powK_ne_zero_of (hG : LocalCohomologySetup.GeoSetupP) (hR : LocalCohomologySetup.ResidAlgP) (hL : LocalCohomologySetup.LocExactP)
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := by
  rcases d with _ | n
  · exact oneK_ne_zero q inferInstance
  · intro h0
    obtain ⟨N, i, hci, hiq, hO⟩ := hD
    obtain ⟨e, he, y, hy, hcov, haff, V, hV, cc, hdom, htc, ht, halg, B, hBr, hBi, hBt, hBfg, hBint, hBle, hBfr⟩ :=
      hG q n N i hci hiq
    let _ : Algebra K Γ(X, V) := (strV q V).toAlgebra
    have _ := hdom
    obtain ⟨Dv, hDv⟩ := GlobalTheory.T.exists_dual_derivations_of_coords q V (n + 1) cc

    have hsQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, T.obj.pdPow (n + 2) = ⊥ := fun T => by
      obtain ⟨k, hk, -⟩ := T.property
      exact hk.1
    have hVQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y),
        σ ≫ D.f = V.ι ∧ InU V ((wU q i y (n + 2)).ι.obj T) := fun T => by
      obtain ⟨k, -, W, ⟨j, rfl⟩, hW⟩ := T.property
      obtain ⟨σ, hσ⟩ := wch_mem D N i hO j
      exact ⟨wch i j, σ, hσ, fun x hx => (hW hx).2⟩
    let Λ : CLiftK (wU q i y (n + 2)).ι D :=
      (GlobalTheory.T.exists_cone_lift q D (n + 2)).some.precomp (ObjectProperty.ιOfLE (wU_le q D i y (n + 2) hO))
    obtain ⟨z, hz, hzf, hzc⟩ := hc (n + 2) _ (wU q i y (n + 2)).ι hsQ hVQ Λ
    obtain ⟨hzp, hzp0⟩ := powK_pull q (wU q i y (n + 2)).ι c z hz hzc (n + 1)
    rw [h0, map_zero] at hzp0
    have hzK : z = zK Λ (n + 2) := funext fun σ => hzf σ
    subst hzK
    obtain ⟨b, hb1, hb, hdiff⟩ := hL q D i hO y hy (n + 2) Λ

    let W := wK q i y (n + 2)
    have hsU : ∀ T, (∃ α, W α T) → (thFil (smFun X q) ((n + 2 : ℕ) : ℤ)).S T = ⊥ := by
      rintro T ⟨k, hk, -⟩
      exact hk.1
    have hvanS : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ),
        Subsingleton (HU (sq (thFil (smFun X q) r) (thFil (smFun X q) (r + 1))) (KS q (n + 2) {⨅ k ∈ S, uy i y k}) j) →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hsub
      obtain ⟨h, hbij⟩ := zar_capS q i y (n + 2) S hS r (r + 1) j
      exact hbij.2.subsingleton
    have : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
    have hvan2 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hr
      refine hvanS S hS r j ?_
      exact gr_top_van q (n + 1) _ (haff S hS) (n + 2) r j (by exact_mod_cast hr)
    have hvan1 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hjr
      rcases lt_or_ge r 0 with hr | hr
      · exact gr_neg_van _ _ r hr j
      rcases le_or_gt r ((n : ℤ) + 1) with hr' | hr'
      · refine hvanS S hS r j ?_
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr
        exact CrystallineSemistableComparison.Pb.gr_aff q _ (haff S hS) (n + 2) m j (by omega) (by omega)
      · exact hvan2 S hS r j hr'
    have hze : CH.d _ 2 (e • zK Λ (n + 2)) = 0 := by rw [map_nsmul, hz, smul_zero]
    have hz1 : ∀ σ, (e • zK Λ (n + 2)) σ ∈ (thFil (smFun X q) 1).S _ := fun σ => by
      have h := mem_pdP_one ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ
        (plogK_mem' ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ (n + 2) (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ))
      exact nsmul_mem h e
    have hzero : ∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T => ∃ α, W α T) ⋙ thA (smFun X q))
        (e • zK Λ (n + 2)) (n + 1)) h = 0 := by
      intro h
      have hsm : cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (e • zK Λ (n + 2)) (n + 1) =
          ((e : K) ^ (n + 1)) • cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (zK Λ (n + 2)) (n + 1) := by
        rw [← Nat.cast_smul_eq_nsmul K, cupPowC_smul]
      have hB := ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hzp).1 hzp0
      refine ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ h).2 ?_
      exact hsm ▸ Submodule.smul_mem _ _ hB
    let ℓ : Fin (n + 1) → CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ thA (smFun X q))) 1 := fun k =>
      resB (thA (smFun X q)) (capS_le_univ W k.castSucc) (b k.castSucc) -
        resB (thA (smFun X q)) (capS_le_univ W k.succ) (b k.succ)
    have hℓcoc : ∀ k, CH.d _ 1 (ℓ k) = 0 := fun k => by
      show CH.d _ 1 (resB _ _ (b k.castSucc) - resB _ _ (b k.succ)) = 0
      rw [map_sub, d_resB, d_resB, ← hb, ← hb]
      exact sub_eq_zero.2 rfl
    have hℓ1 : ∀ k σ, ℓ k σ ∈ (sFil (capS W Finset.univ) 1).S _ := fun k σ => by
      have h1 := hb1 k.castSucc (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.castSucc))
      have h2 := hb1 k.succ (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.succ))
      exact Ideal.sub_mem ((thFil (smFun X q) 1).S (σ.obj (Fin.last 1)).obj) h1 h2
    have hc0' : ∃ c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
        Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS W Finset.univ).ι)
          ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (cupListC ((capS W Finset.univ).ι ⋙ (thP (smFun X q)).A) ℓ) c0 := by
      have := rep_cupList (sP (capS W Finset.univ)) (sFil (capS W Finset.univ)) (isFil _) ℓ hℓcoc hℓ1
      rw [Nat.cast_succ] at this
      exact this
    obtain ⟨c0, hc0⟩ := hc0'
    obtain ⟨ω, f, hf, hdf, hrep⟩ := cech_top_rel (thP (smFun X q)) (thFil (smFun X q)) (isFil_th _) (n + 2) n W hsU
      (wK_rel q i y (n + 2)) hvan1 hvan2 (e • zK Λ (n + 2)) hze hz1 b hb1 hb hzero c0 hc0
    have key : ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
        (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
        ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
      have hKG : KH.LocGr := CrystallineSemistableComparison.Pb.loc_gr
      have hKP : KH.PolyTf := CrystallineSemistableComparison.Pb.poly_tf
      have hKA : KH.GrAff := CrystallineSemistableComparison.Pb.gr_aff
      have hV' : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k := fun S => le_biInf_of_le hV S
      have hUk : ∀ k, (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) ≤ uy i y k := fun k =>
        biInf_le _ (Finset.mem_univ k)
      let g : Fin (n + 1) → Γ(X, ⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) := fun k =>
        (i.appLE _ _ (hUk k.succ)).hom (yQ y hy k.castSucc k.succ)
      have hg : ∀ k, IsUnit (g k) := fun k => yQ_unit i y hy _ _ _ (hUk _) (hUk _)
      choose ĝ0 hĝ0 hĝd using hdiff
      let ĝ : Fin (n + 1) → ∀ T : (capS W Finset.univ).FullSubcategory, T.obj.B := fun k T =>
        ĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩
      have hĝ : ∀ k T (h : InU (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) T.obj),
          Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k) := fun k T h => by
        have h1 : InU (uy i y k.succ) T.obj := inU_mono q (hUk k.succ) h
        have e1 := hĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩ h1
        have e2 := rs_appLE i (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ))
          (hUk k.succ) le_rfl (yQ y hy k.castSucc k.succ)
        have e3 := ev_rs T.obj (hUk k.succ) h h1
          ((i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ)) (uy i y k.succ)
            le_rfl).hom (yQ y hy k.castSucc k.succ))
        refine e1.trans (e3.symm.trans ?_)
        exact congrArg (ev T.obj h) e2
      have hℓeq : ℓ = fun k => dlogC (capS W Finset.univ) (n + 2) (ĝ k) := funext fun k =>
        congrArg (resB (thA (smFun X q))
          (fun T h α _ => h α (Finset.mem_univ α) : capS W Finset.univ ≤ capS W {k.castSucc, k.succ})) (hĝd k.castSucc k.succ)
      rw [hℓeq] at hc0
      obtain ⟨x, η, hx, hη, heq⟩ := cone_transfer hKG hKP hKA q n i y haff V hV' cc Dv hDv g hg ĝ hĝ c0 hc0 ω f hf hdf hrep
      let tu : Fin (n + 1) → Γ(X, V)ˣ := fun k => (ht k).unit
      let g' : Fin (n + 1) → Γ(X, V) := fun k => if h : (k : ℕ) = 0 then (((tu 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (tu ⟨k - 1, by omega⟩ : Γ(X, V)) * (((tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V))
      have hgt : ∀ k, rs (hV' Finset.univ) (g k) = g' k := fun k =>
        g_rel i y hy V _ (hV' Finset.univ) hUk tu (fun k => by simp only [tu, IsUnit.unit_spec]; exact htc k) k
      have hDvu : ∀ k j, Dv k (tu j) = if k = j then 1 else 0 := fun k j => by simpa [tu] using hDv k j
      have hdr : Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = (((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) ∨
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = -(((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) :=
        dlog_ratios n tu Dv hDvu
      have hL : Ring.inverse (∏ k, rs (hV' Finset.univ) (g k)) *
          (Matrix.of fun k l => Dv k (rs (hV' Finset.univ) (g l))).det =
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det := by simp only [hgt]
      rw [hL] at heq
      have hne : ∀ j : Fin (n + 2), (Finset.univ.erase j).Nonempty := fun j =>
        ⟨j.succAbove 0, Finset.mem_erase.2 ⟨Fin.succAbove_ne j 0, Finset.mem_univ _⟩⟩
      have hxm : ∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id := fun j =>
        jacSpan_le (hV' _) (B _) (hBr _ (hne j)) Dv id (hx j)
      have hηm : ∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k) := fun k =>
        jacSpan_le (hV' _) (B _) (hBr _ Finset.univ_nonempty) Dv _ (hη k)
      have hneg : (∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          (-(((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k))) →
          ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
        rintro ⟨x, η, hx, hη, he⟩
        refine ⟨fun j => -x j, fun k => -η k, fun j => (jacS _ Dv id).neg_mem (hx j),
          fun k => (jacS _ Dv _).neg_mem (hη k), ?_⟩
        rw [← neg_neg (((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)), he]
        simp only [map_neg, mul_neg, Finset.sum_neg_distrib, neg_add]
      rcases hdr with hd | hd <;> rw [hd] at heq <;> rcases heq with he | he
      · exact ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact ⟨x, η, hxm, hηm, by rw [← he, neg_neg]⟩
    obtain ⟨x, η, hx, hη, heq⟩ := key
    refine hR K n Γ(X, V) (fun k => (ht k).unit) (by simpa using halg) Dv (by simpa using hDv) B hBt hBfg hBint
      hBle hBfr x η hx hη heq

end CrystallineSemistableComparison.Pb
