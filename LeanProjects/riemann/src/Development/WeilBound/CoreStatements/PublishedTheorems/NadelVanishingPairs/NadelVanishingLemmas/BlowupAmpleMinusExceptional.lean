import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveCartierLocalEquation
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.IdealSectionsLocallyGenerated
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.IdealPullbackLocallyGenerated

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistBelow

theorem l1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData), FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧ ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0), J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := GlobalTheory.T.effective_cartier_local_equation

theorem l2 : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := GlobalTheory.T.ideal_sections_locally_generated

theorem l3 : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := GlobalTheory.T.ideal_pullback_locally_generated

theorem isGenerated_of_sections {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {n : ℕ}
    (f : Fin n → Y.functionField) (hf : ∀ k, f k ∈ D.sections) (hg : ∀ y, ∃ k, D.GeneratesAt y (f k))
    (P : LB Y) (hP : P.IsLB) (e : cls P hP = toPic D) : IsGenerated P := by
  have h := presents_toLB D
  let s : Fin n → (toLB D).Sec := fun k => h.secEquiv.symm ⟨f k, hf k⟩
  have hs : ∀ k, h.rat (s k) = f k := by
    intro k
    rw [← h.coe_secEquiv]
    simp [s]
  have hgen : IsGenerated (toLB D) := by
    refine ⟨n, s, ?_⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hg y
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, (h.generatesAt_rat_iff (s k)).1 (by rw [hs]; exact hk)⟩
  have hiso : LBIso P (toLB D) := (cls_eq_iff hP (isLB_toLB D)).1 (e.trans h.toPic_eq)
  exact hgen.of_lbIso hP hiso

private theorem fnOf_div_eq_fnOf_div_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (i j : L.ι)
    (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    fnOf (L.U i) hi (s.f i) / r i = fnOf (L.U j) hj (s.f j) / r j := by
  have hij : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have hr := h.isRatSec i j hij
  have hc := congrArg (fnOf (L.U i ⊓ L.U j) hij) (s.compat i j)
  simp only [map_mul] at hc
  simp only [fnOf, TopCat.Presheaf.germ_res_apply] at hc hr ⊢
  rw [hc, hr]
  have hne : (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 := by
    intro h0
    have := congrArg (fun z => z * (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      ((L.g i j)⁻¹ : (Γ(X, L.U i ⊓ L.U j))ˣ)) h0
    simp only [zero_mul, ← map_mul, Units.mul_inv, map_one] at this
    exact one_ne_zero this
  rw [mul_div_mul_left _ _ hne]

private theorem Presents_rat_eq_fnOf_div {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (j : L.ι)
    (hj : genericPoint X ∈ L.U j) :
    h.rat s = fnOf (L.U j) hj (s.f j) / r j := by
  simp only [Presents.rat, LinearMap.coe_mk, AddHom.coe_mk]
  exact fnOf_div_eq_fnOf_div_of_presents h s _ j _ hj

theorem exists_eff_isGenerated : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  intro Y₀ Y₁ _ _ t I hEff A hA
  obtain ⟨E, hEeff, hEsupp, hEq⟩ := l1 Y₁ (I.comap t) hEff
  refine ⟨E, hEeff, hEsupp, ?_⟩
  filter_upwards [hA.eventually_isGloballyGenerated_twist (idealModule I)] with c hc
  intro P hP hcls
  have hM : (lbPow A c).IsLB := isLB_lbPow hA.isLB c
  obtain ⟨n, σ, hσ1, hσ2⟩ := l2 Y₀ (lbPow A c) hM I hc
  have hL : ((lbPow A c).pull t).IsLB := LB.isLB_pull hM t
  have hcov : ∀ y : Y₁, ∃ j, y ∈ ((lbPow A c).pull t).U j := by
    intro y
    have : y ∈ ⨆ i, ((lbPow A c).pull t).U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨i₀, hi₀⟩ := hcov (genericPoint Y₁)
  have h := presents_ofLB hL i₀ hi₀
  have hcls' : cls P hP = toPic (ofLB hL i₀ hi₀ - E) := by
    rw [map_sub, h.toPic_eq, cls_pull hM t, cls_lbPow hA.isLB c, hcls, map_nsmul]
  have key : ∀ y : Y₁, ∃ g : (Y₁.functionField)ˣ, (ofLB hL i₀ hi₀ - E).IsEqn y g ∧
      (∀ k, RegAt y (h.rat (secPull (σ k) t) * g)) ∧ ∃ k, UnitAt y (h.rat (secPull (σ k) t) * g) := by
    intro y
    obtain ⟨j, hj⟩ := hcov y
    have hx : t y ∈ (lbPow A c).U (j PUnit.unit) := Set.mem_iInter.1 hj PUnit.unit
    have hV : ((lbPow A c).pull t).U j ≤ t ⁻¹ᵁ (lbPow A c).U (j PUnit.unit) :=
      fun z hz => Set.mem_iInter.1 hz PUnit.unit
    obtain ⟨U', f, hyU', hfnzd, hspan⟩ := hEff y
    have hf : fnOf U'.1 (gen_mem hyU') f ≠ 0 := by
      haveI : Nonempty U'.1 := ⟨⟨y, hyU'⟩⟩
      intro h0
      rw [← map_zero (fnOf U'.1 (gen_mem hyU'))] at h0
      exact nonZeroDivisors.ne_zero hfnzd (fnOf_injective _ _ h0)
    have hEy := hEq y U' f hyU' hf hspan
    have hDy := (h.isEqn j y hj).sub hEy
    obtain ⟨hreg, hunit⟩ := l3 Y₀ Y₁ t I y ((lbPow A c).U (j PUnit.unit)) hx n
      (fun k => (σ k).f (j PUnit.unit)) (fun k W hW => hσ1 k _ W hW)
      (fun W hxW a ha => hσ2 (t y) _ hx W hxW a ha) U' f hyU' hf hspan _ hV hj
    have hrat : ∀ k, h.rat (secPull (σ k) t) * ↑(frameRat _ i₀ hi₀ j / Units.mk0 _ hf) =
        fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) /
          fnOf U'.1 (gen_mem hyU') f := by
      intro k
      rw [Presents_rat_eq_fnOf_div h _ j (gen_mem hj)]
      have he : fnOf _ (gen_mem hj) ((secPull (σ k) t).f j) =
          fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) := rfl
      rw [he]
      have hr0 : ((frameRat _ i₀ hi₀ j : (Y₁.functionField)ˣ) : Y₁.functionField) ≠ 0 := Units.ne_zero _
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    exact ⟨_, hDy, fun k => by rw [hrat]; exact hreg k,
      by obtain ⟨k, hk⟩ := hunit; exact ⟨k, by rw [hrat]; exact hk⟩⟩
  apply isGenerated_of_sections (ofLB hL i₀ hi₀ - E) (fun k => h.rat (secPull (σ k) t)) _ _ P hP hcls'
  · intro k
    rw [CartierDiv.mem_sections]
    intro y
    obtain ⟨g, hg, hreg, -⟩ := key y
    exact hg.regularAt_iff.2 (hreg k)
  · intro y
    obtain ⟨g, hg, -, k, hk⟩ := key y
    exact ⟨k, hg.generatesAt_iff.2 hk⟩

end GlobalTheory.TwistBelow
