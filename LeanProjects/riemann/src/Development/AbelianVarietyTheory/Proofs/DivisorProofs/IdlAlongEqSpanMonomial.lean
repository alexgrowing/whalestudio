import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartIdeal

theorem dvd_of_map_dvd {R R' : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing R'] [IsDomain R']
    (ρ : R →+* R') (hρ : Function.Injective ρ) (hi : ρ.IsIntegral) {f x : R} (hf : f ≠ 0) (h : ρ f ∣ ρ x) : f ∣ x := by
  obtain ⟨s, hs⟩ := h
  let K := FractionRing R
  let K' := FractionRing R'
  have hj := IsFractionRing.injective R K
  have hfK : algebraMap R K f ≠ 0 := (map_ne_zero_iff _ hj).2 hf
  let σ : K →+* K' := GlobalTheory.ArcPull.fracMap hρ
  have hσ : ∀ r, σ (algebraMap R K r) = algebraMap R' K' (ρ r) := GlobalTheory.ArcPull.fracMap_algebraMap hρ
  have e : σ (algebraMap R K x / algebraMap R K f) = algebraMap R' K' s := by
    rw [map_div₀, div_eq_iff ((map_ne_zero σ).2 hfK), hσ, hσ, hs, map_mul, mul_comm]
  obtain ⟨p, hp, hp0⟩ := hi s
  have hint : IsIntegral R (algebraMap R K x / algebraMap R K f) := by
    refine ⟨p, hp, σ.injective ?_⟩
    rw [Polynomial.hom_eval₂, e, map_zero, show σ.comp (algebraMap R K) = (algebraMap R' K').comp ρ from RingHom.ext hσ,
      ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨r, hj (by rw [map_mul, hr, mul_div_cancel₀ _ hfK])⟩

theorem eq_span_of_forall_cdvr {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [CommRing R']
    [IsDomain R'] [IsLocalRing R'] (hR' : IsCN R') (ρ : R →+* R') (hρ : Function.Injective ρ) (hi : ρ.IsIntegral)
    (hl : IsLocalHom ρ) (I : Ideal R) {f : R} (hf : f ≠ 0)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : R' →+* V), GlobalTheory.LN.CDvr V → Function.Injective ψ →
      IsLocalHom ψ → (I.map ρ).map ψ = Ideal.span {ψ (ρ f)}) : I = Ideal.span {f} := by
  obtain ⟨_, _, -, _⟩ := hR'
  have loc : ∀ (V : Type) [CommRing V] [IsLocalRing V] (ψ : R' →+* V), (maximalIdeal V).comap ψ = maximalIdeal R' →
      IsLocalHom ψ := fun V _ _ ψ h => ((IsLocalRing.local_hom_TFAE ψ).out 0 4).2 h
  have hdvd : ∀ x ∈ I, f ∣ x := fun x hx => by
    refine dvd_of_map_dvd ρ hρ hi hf (GlobalTheory.ValCrit.dvd_of_forall_cdvr R' _ _ ((map_ne_zero_iff _ hρ).2 hf)
      fun V _ _ _ ψ hV hψ hc => ?_)
    rw [← Ideal.mem_span_singleton, ← H V ψ hV hψ (loc V ψ hc)]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
  refine le_antisymm (fun x hx => Ideal.mem_span_singleton.2 (hdvd x hx)) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra hfI
  have hle : I ≤ Ideal.span {f} * maximalIdeal R := fun x hx => by
    obtain ⟨c, rfl⟩ := hdvd x hx
    refine Ideal.mem_span_singleton_mul.2 ⟨c, fun hc => hfI ?_, rfl⟩
    obtain ⟨c', hc'⟩ := hc.exists_right_inv
    have := I.mul_mem_right c' hx
    rwa [_root_.mul_assoc, hc', _root_.mul_one] at this
  obtain ⟨V, _, _, _, ψ, hV, hψ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
  have := loc V ψ hc
  have h₁ : ψ (ρ f) ∈ Ideal.span {ψ (ρ f)} * maximalIdeal V := by
    have h₂ : ψ (ρ f) ∈ (I.map ρ).map ψ := by rw [H V ψ hV hψ this]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.map_map] at h₂
    refine (Ideal.map_le_iff_le_comap.2 fun x hx => ?_ : I.map (ψ.comp ρ) ≤ _) h₂
    obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 (hle hx)
    refine Ideal.mem_span_singleton_mul.2 ⟨ψ (ρ c), ?_, by simp⟩
    exact (map_mem_nonunits_iff ψ _).2 ((map_mem_nonunits_iff ρ _).2 hc)
  obtain ⟨z, hz, e⟩ := Ideal.mem_span_singleton_mul.1 h₁
  have h0 : ψ (ρ f) ≠ 0 := (map_ne_zero_iff _ hψ).2 ((map_ne_zero_iff _ hρ).2 hf)
  rw [mul_eq_left₀ h0] at e
  exact hz (e ▸ isUnit_one)

theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (hR : IsCN R) (hR' : IsCN R') (g : R →+* R') (hg : Function.Injective g) (hl : IsLocalHom g)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) :
    ∃ (D' : DegData R' (maximalIdeal R')) (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif (maximalIdeal R') D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left),
      IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) := by
  obtain ⟨h1, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  have aR' : AdmBase R' (maximalIdeal R') := ⟨hR'.1, inferInstance, hR'.2.1, hR'.2.2.1⟩
  have hI : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff g a).2 ha
  have sq : spMap (GlobalTheory.ArcPull.fracMap hg) ≫ jK R = jK R' ≫ spMap g :=
    (GlobalTheory.ArcPull.fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := h1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (Geo.Tor.chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (Geo.Tor.chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact GlobalTheory.PolBaseChange.eSec_comm (isGrpPullback_pullback G (spMap g))
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R _ aR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, -, -⟩ := h4.unifBaseChange R R' _ _ aR aR' g hI D A G hG U Wo hψ hgen
    ((Over.pullback (specOf g)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (Geo.Tor.idIso _) he
    (Geo.Tor.idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

theorem tauCoord_unique {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X)
    (k k' : (FractionRing R)ˣ) (h : Q.TauCoord a b k) (h' : Q.TauCoord a b k') :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (k : FractionRing R) * algebraMap R _ x = k' * algebraMap R _ x' := by
  obtain ⟨u, hu, e⟩ := h
  obtain ⟨u', hu', e'⟩ := h'
  obtain ⟨jj, hjj⟩ := GlobalTheory.TauLocal.exists_chart_all Q.M
  have key : ∀ (p q : 𝟙_ (Over (Sp R)) ⟶ Q.B) (t : LB.Gen (LB.LinComb Q.M.L (lamPts p q) negε)), t.IsGen →
      ∃ w : Γ(Sp R, ⊤)ˣ, ∀ z J, Good Q.M.L z J → val t (toUnit (TK R)).left z J =
        gm (𝟙 (TK R).left) z ⊤ (InhTate.pullTop (jK R) w) * ∏ i, (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
          (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ))) (lamPts p q i) ^ negε i := by
    intro p q t ht
    have htop : (⊤ : (𝟙_ (Over (Sp R))).left.Opens) ≤ LB.wchart Q.M.L (lamPts p q) (fun i => jj (lamPts p q i)) :=
      fun y _ => Set.mem_iInter.2 fun i => hjj _ y
    refine ⟨res htop (t.s (fun i => jj (lamPts p q i))), fun z J hJ => ?_⟩
    refine (gen_trans ht _ z (hJ.mem _ _) (htop trivial)).trans ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gm_res _ z htop trivial _).symm.trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK R) z ⊤ trivial _).symm)
    rfl
  obtain ⟨w, hw⟩ := key _ _ u hu
  obtain ⟨w', hw'⟩ := key _ _ u' hu'
  have k₁ : unitOn k * InhTate.pullTop (jK R) w = unitOn k' * InhTate.pullTop (jK R) w' :=
    GlobalTheory.TauLocal.eq_of_gm Q.M.isLB fun z J hJ => by
    have s := (e z J hJ).symm.trans (e' z J hJ)
    rw [hw z J hJ, hw' z J hJ, ← _root_.mul_assoc, ← _root_.mul_assoc] at s
    rw [map_mul, map_mul]
    exact mul_right_cancel s
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w'.val,
    w.isUnit.map _, w'.isUnit.map _, ?_⟩
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w'))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k'.val

theorem exists_pos {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {Q : Data R} (hQ : Q.IsPos (maximalIdeal R)) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ Q.X} (h : Q.IsMonomialTau t β) (h₀ : ∀ i y, 0 ≤ β i y y) (y : Q.X)
    (hy : y ≠ 0) : ∃ i, 0 < β i y y := by
  by_contra hne
  have hz : ∀ i, β i y y = 0 := fun i => le_antisymm (not_lt.1 (not_exists.1 hne i)) (h₀ i y)
  obtain ⟨r, hr, k, hk, hc⟩ := hQ y hy
  obtain ⟨k', hk', hc'⟩ := h y y
  obtain ⟨x, x', -, hx', e⟩ := tauCoord_unique Q y y k k' hc hc'
  simp only [hz, zpow_zero, Finset.prod_const_one] at hk'
  rw [hk, hk', _root_.one_mul, ← map_mul] at e
  rw [← IsFractionRing.injective R (FractionRing R) e] at hx'
  exact hr (isUnit_of_mul_isUnit_left hx')

theorem idlAlong_eq_span_monomial : ∀ (g : ℕ) (n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (d : ℕ) (J : Z.IdealSheafData), ValOn F i φ J d → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (b : cycAway n →+* R) (a : Sp R ⟶ Z) (Q : Data R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGenFibre F y α₁ → jK R ≫ a = y ≫ i → IsMumfordFam F y α₁ Q → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (e : Fin m → ℕ), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → IsCone id φ δ → (∀ w, w ≠ 0 → ∃ k, 0 < δ k w w) → Q.IsMonomialTau t (fun k => (n : ℤ) • δ k) → (∀ k, (e k : ℝ) = d * φ.evalZ ((n : ℤ) • δ k)) → idlAlong J a = Ideal.span {∏ k, t k ^ e k} := by
  intro g n F Z i φ _ d J hJ R _ _ _ _ _ b a Q G₁ _ _ y α₁ hG₁ _ ha hM m t δ e ht _ hδ _ hmon he
  have hCN := hM.isCN
  have := hCN.2.1
  have ht0 : ∀ k, t k ≠ 0 := ne_zero_of_isRelParam ht
  have hsym : ∀ k u v, ((n : ℤ) • δ k) u v = ((n : ℤ) • δ k) v u := fun k u v => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem k)) u v]
  have hnn : ∀ k u, 0 ≤ ((n : ℤ) • δ k) u u := fun k u => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg k u)
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    refine_monomial_of_polarised R Q m t (fun k => (n : ℤ) • δ k) hCN hmon ht.1 ht0 hsym hnn (exists_pos hM.isPos hmon hnn)
  obtain ⟨G', _, _, π, A, U, hπ, κ, πK, α, α₂, hκ, -, hA, hsq, hL, -⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  have hG' : IsSemiAbelian G' := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hπ (isGrpPullback_pullback G₁ (spMap ρ))
    exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback _ G₁ hG₁)
  refine eq_span_of_forall_cdvr hCN' ρ hinj hfin.to_isIntegral hloc _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht0 k)) fun V _ _ _ ψ hV hψ hψl => ?_
  obtain ⟨_, hVc, _⟩ := hV
  obtain ⟨D', hD, A', U', gA, hgA, hLA⟩ := exists_pull hCN' ⟨inferInstance, inferInstance, hVc, inferInstance⟩ ψ hψ hψl hG' U
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hψr : ∀ k, ψ (r k) ≠ 0 := fun k h => ht0 k (hinj (by
    rw [← hr, (map_eq_zero_iff _ hψ).1 h, map_zero]; simp))
  choose w v hv using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψr k) hϖ
  have hprod : ∀ x : Fin m → ℕ, ∏ k, ψ (r k) ^ x k = ((∏ k, v k ^ x k : Vˣ) : V) * ϖ ^ ∑ k, w k * x k := fun x => by
    rw [← Finset.prod_pow_eq_pow_sum, Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hv, mul_pow, pow_mul, Units.val_pow_eq_pow_val]
  let θ : D'.toPre.X ≃ₗ[ℤ] Q.X := (hD.xe.trans ε).toIntLinearEquiv
  let β₀ : LinearMap.BilinForm ℤ Q.X := ∑ k, ((2 * w k : ℕ) : ℤ) • ((n : ℤ) • δ k)
  have hβ₀ : ∀ u u', β₀ u u' = ∑ k, ((2 * w k : ℕ) : ℤ) * ((n : ℤ) • δ k) u u' := fun u u' => by
    simp only [β₀, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have sq := GlobalTheory.LamPull.exists_isSquare hgA.1.w
  letI := A.isAb.comm
  letI := A'.isAb.comm
  have i₁ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  let T : Trait F :=
    { V := V, complete := hVc, ϖ := ϖ, irr := hϖ, y := spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ κ ≫ y
      G := (Over.pullback (spMap ψ)).obj G', semi := IsSemiAbelian.pullback _ G' hG', D := D', A := A', U := U'
      α := gA ≫ α, α₂ := _, cart := hgA.comp hA, sq := isSquare_comp sq hsq
      lb := LBIso.trans (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB i₁ _) (pull_isLB F.univ.isLB _)
        (GlobalTheory.LamPull.lbIso_lam_pull hgA A.isLB A'.isLB hLA sq) (lbIso_pull_comp hL _ rfl)
      β := pull θ.toLinearMap β₀
      symm := fun u u' => by
        show β₀ _ _ = β₀ _ _
        rw [hβ₀, hβ₀]
        exact Finset.sum_congr rfl fun k _ => by rw [hsym]
      mono := fun u => by
        obtain ⟨u₁, x, hx, hc⟩ := hmon' (hD.xe u)
        obtain ⟨u₂, hc'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD u _ hc
        refine ⟨u₂ * Units.map (ψ : R' →* V) u₁ * ∏ k, v k ^ x k, ![∑ k, w k * x k], fun l => ?_, ?_⟩
        · rw [Subsingleton.elim l 0]
          show β₀ (θ u) (θ u) = 2 * ((∑ k, w k * x k : ℕ) : ℤ)
          rw [hβ₀]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have h₁ : 2 * ((n : ℤ) • δ k) (θ u) (θ u) = 2 * (x k : ℤ) := hx k
          rw [mul_left_cancel₀ two_ne_zero h₁]
          ring
        · convert hc' using 1
          rw [map_mul, map_prod]
          simp_rw [map_pow]
          rw [hprod]
          simp [_root_.mul_assoc] }
  have hfr : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK R' = jK V ≫ spMap ψ :=
    (GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)
  obtain ⟨c, hc, hI⟩ := hJ T (spMap ψ ≫ spMap ρ ≫ a) (by
    show jK V ≫ _ = (spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ κ ≫ y) ≫ i
    rw [Category.assoc, Category.assoc, ← ha, reassoc_of% hκ, reassoc_of% hfr])
  have hc' : (c : ℝ) = d * φ.evalZ (pull θ.toLinearMap β₀) := hc
  have hev : φ.evalZ β₀ = ∑ k, ((2 * w k : ℕ) : ℝ) * φ.evalZ ((n : ℤ) • δ k) := by
    rw [← hδ.linearOn_smul n (fun k => ((2 * w k : ℕ) : ℝ)) (fun k => by positivity)]
    unfold InvFun.evalZ
    congr 1
    funext u u'
    rw [hβ₀]
    push_cast
    rfl
  have hce : c = ∑ k, w k * (2 * e k) := by
    rw [evalZ_pull φ θ.surjective, hev, Finset.mul_sum] at hc'
    apply Nat.cast_injective (R := ℝ)
    rw [hc']
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [he]; ring
  have hI' : idlAlong J (spMap ψ ≫ spMap ρ ≫ a) = Ideal.span {ϖ ^ c} := hI
  rw [GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp] at hI'
  rw [hI', map_prod, map_prod]
  simp_rw [map_pow, ← hr, map_pow, ← pow_mul]
  rw [hprod, hce]
  exact (Ideal.span_singleton_mul_left_unit (Units.isUnit _) _).symm

end GlobalTheory.ChartIdeal
