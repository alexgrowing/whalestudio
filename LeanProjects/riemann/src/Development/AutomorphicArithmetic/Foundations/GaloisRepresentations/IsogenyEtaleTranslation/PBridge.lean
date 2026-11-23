import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)
open UpperTheory.Gal.LocalSmoothExtension (qAt al leg cW CxFin StdC)

namespace UpperTheory.Gal.FixZ

private theorem lev_eq {G : Type} [Group G] (K : Subgroup G) (h : G) :
    GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ = G3.lev K h := by
  ext x
  simp only [GlobalTheory.HeckeCorr.heckeLevel, G3.lev, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨hx, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · rintro ⟨hx, hy⟩
    refine ⟨hx, _, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem ind_eq {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Formalism.UG.dosetInd ℂ K g = G3.ind ℂ K g := by
  rfl

private theorem smooth_iso {A B C : Scheme.{0}} (e : A ≅ B) (s : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n s) : SmoothOfRelativeDimension n (e.hom ≫ s) := by
  haveI := h
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) e.hom s
  rwa [Nat.zero_add] at this

end UpperTheory.Gal.FixZ

open UpperTheory.Gal UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.bridge_of :
    UpperTheory.Gal.FixZ.TrFEt → UpperTheory.Gal.FixZ.AlFEt → UpperTheory.Gal.FixZ.LegOf → UpperTheory.Gal.FixZ.WtEq → UpperTheory.Gal.FixZ.TanIso → UpperTheory.Gal.FixZ.DimUniq → UpperTheory.Gal.FixZ.CxFinOf → UpperTheory.Gal.FixZ.Bridge := by
  intro hTr hAl hLeg hWt hTan hDim hCx h0 hZ p _ D G L hSc gb hStd i₀ v hv k T N' N hdvd d hsm h a b hreg α hα
  have hτ : ∀ i, D.tau i = D.tau i₀ := fun i => by
    have : Subsingleton (Fin D.a) := by rw [hSc.a1]; infer_instance
    rw [Subsingleton.elim i i₀]
  have hAdm : ∀ u ∈ L.KN N'.1, h * u * h⁻¹ ∈ L.KN N.1 := fun u hu => by
    have := b.2 u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at this
  have hLe : L.KN N'.1 ≤ L.KN N.1 := fun u hu => by
    have := a.2 u (by rw [T.K_eq]; exact hu)
    rw [T.K_eq] at this
    simpa using this
  have hLev : W2.LevOk L N.1 N'.1 h := ⟨N.2.1, N.2.2, N'.2.1, N'.2.2, hdvd, hAdm⟩
  obtain ⟨c₁, hc₁, -⟩ := hLeg p D G L gb k T N' N 1 a
  obtain ⟨c₂, -, hc₂'⟩ := hLeg p D G L gb k T N' N h b
  have hc₂ := hc₂' α
  have hregZ : ∀ g, h * g ∈ L.KN N.1 → GlobalTheory.LKCx.RegAf G g := fun g hg => hreg g (by
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N.1 : Set G.GAf) (L.KN N.1) :=
      DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, h * g, hg, by simp⟩
    rw [G3.ind, Set.indicator_of_mem hm]
    exact one_ne_zero)
  have heq : ∀ M : Lv p, (T.e M).hom ≫ W2.sZ (T.M M) k = qAt T M := T.e_q
  have hpw : c₁.pw k = (T.e N').inv ≫ T.X.tr _ _ 1 a.1 a.2 ≫ (T.e N).hom := by
    rw [hc₁, Iso.inv_hom_id_assoc]
  have htw : c₂.tw α = (T.e N').inv ≫ leg T N' N h b α ≫ (T.e N).hom := by
    rw [hc₂, Iso.inv_hom_id_assoc]
  have hEt : Etale (c₁.pw k) := by
    haveI := T.X.etale (T.lev N') (T.lev N) a.1 a.2
    rw [hpw]
    infer_instance
  have h₁ : c₁.pw k ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [hpw, Category.assoc, Category.assoc, heq N, T.X.tr_q, Iso.inv_comp_eq]
    exact (heq N').symm
  have h₂ : c₂.tw α ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [htw, Category.assoc, Category.assoc, heq N, LocalSmoothExtension.leg_q, Iso.inv_comp_eq]
    exact (heq N').symm
  obtain ⟨-, -, -, -, -, hfin, hone, -⟩ := h0 p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  obtain ⟨hsm₀, Fx, At, hFx, hAt, hSum⟩ := hZ p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  have hRHS : ∀ y : ℂ, ∑ x ∈ Fx, W2.lefTerm (At x) y =
      (((L.KN N'.1).relIndex (G3.lev (L.KN N.1) h) : ℕ) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (G3.ind ℂ (L.KN N.1) h⁻¹) (LocalSmoothExtension.Kp G) (LocalSmoothExtension.oneP G) := by
    intro y
    rw [hSum y, hWt p D G L hSc.a1 i₀ v hv k α y, lev_eq, ind_eq]
    rfl
  have hFT := hTr p D G L gb k T N' N h b.1 b.2
  have hFA := hAl p D G L gb k T N α (fun s => (hα s).1)
  have hlegF : IsFinite (leg T N' N h b α) := by
    haveI := hFT.1
    haveI := hFA.1
    unfold leg
    infer_instance
  have hlegE : Etale (leg T N' N h b α) := by
    haveI := hFT.2
    haveI := hFA.2
    unfold leg
    infer_instance
  refine ⟨hCx p G v (L.KN N.1) (L.KN N'.1) h hLe hAdm hfin hone, hlegF, hlegE, ?_⟩
  by_cases hne : Nonempty (T.X.Z (T.lev N))
  · have hsm₁ : SmoothOfRelativeDimension (D.n - 1 + k * D.g) (qAt T N) := by
      rw [← heq N]
      exact smooth_iso _ _ _ hsm₀
    have hd : d = D.n - 1 + k * D.g := hDim _ (qAt T N) _ _ hsm hsm₁ hne
    subst hd
    obtain ⟨E, -, hE2, hE3⟩ := hTan _ _ _ _ (qAt T N) (qAt T N') (W2.sZ (T.M N) k) (W2.sZ (T.M N') k) (T.e N) (T.e N')
      (heq N) (heq N') (D.n - 1 + k * D.g) (T.X.tr _ _ 1 a.1 a.2) (leg T N' N h b α) (c₁.pw k) (c₂.tw α)
      (T.X.tr_q _ _ 1 a.1 a.2) (LocalSmoothExtension.leg_q T N' N h b α) h₁ h₂ hc₁ hc₂
    have hmem : ∀ x, x ∈ Fx.map E.symm.toEmbedding ↔ E x ∈ Fx := fun x => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
    refine ⟨Fx.map E.symm.toEmbedding, fun x => At (E x), fun x => ?_, fun x hx => ?_, fun y => ?_⟩
    · rw [hmem, hFx, hE2]
    · have := hAt _ ((hmem x).1 hx)
      exact ⟨hE3 x _ this.1, this.2⟩
    · rw [← hRHS y, Finset.sum_map]
      simp
  · have hpt : ∀ _ : Sp ℂ ⟶ T.X.Z (T.lev N'), False := fun x =>
      hne ⟨(x ≫ T.X.tr _ _ 1 a.1 a.2) (IsLocalRing.closedPoint ℂ)⟩
    have hFx0 : Fx = ∅ := Finset.eq_empty_of_forall_notMem fun x _ => hpt (x.1 ≫ (T.e N').inv)
    refine ⟨∅, fun _ => 0, fun x => (hpt x.1).elim, fun x => (hpt x.1).elim, fun y => ?_⟩
    rw [← hRHS y, hFx0, Finset.sum_empty, Finset.sum_empty]

end
