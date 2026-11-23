import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelFourier

theorem charSum (M K : ℕ) (hM : M ≠ 0) (z : Fin K → ℂ) (hz : ∀ i, z i ^ M = 1) :
    ∑ c : Fin K → Fin M, ∏ i, z i ^ (c i : ℕ) = if ∀ i, z i = 1 then (M : ℂ) ^ K else 0 := by
  rw [← Fintype.prod_sum (fun i (j : Fin M) => z i ^ (j : ℕ))]
  have h1 : ∀ i, ∑ j : Fin M, z i ^ (j : ℕ) = if z i = 1 then (M : ℂ) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => z i ^ j) M]
    split_ifs with h
    · simp [h]
    · rw [geom_sum_eq h, hz i, sub_self, zero_div]
  simp only [h1]
  split_ifs with h
  · simp [h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

open GlobalTheory.LatFinMod GlobalTheory.LatVac in

theorem gens (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ (K : ℕ) (g : Fin K → WO S T),
      (∀ i, g i ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧
      ∀ k : ℕ, 0 < k → ∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ n : Fin K → ℤ, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          w = ∑ i, n i • g i + k • u := by
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun _ => True
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ G, x ∈ Λ := by
    rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
  obtain ⟨K, g, hg⟩ := hG.fin_embedding
  refine ⟨K, g, fun i => hGΛ _ (hg ▸ Set.mem_range_self i), fun k hk w hw => ?_⟩
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  rw [← hg] at hy
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  exact ⟨n, u, hu, by rw [hn]⟩

theorem root_mem {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {M : ℕ} (hM : M ≠ 0) {O : Subring ℂ} (hz : zeta M ∈ O)
    {t y : WO S T} (ht : t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : M • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplO S T t y) ^ M = 1 ∧ ψ (symplO S T t y) ∈ O := by
  have h1 : ψ (symplO S T t y) ^ M = 1 := by
    have e1 : symplO S T t (M • y) = M • symplO S T t y :=
      (AddMonoidHom.mk' (symplO S T t) (GlobalTheory.PlaceModel.symplO_add_right S T t)).map_nsmul M y
    rw [← AddChar.map_nsmul_eq_pow, ← e1]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT ht hy
  refine ⟨h1, ?_⟩
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp M hM).eq_pow_of_pow_eq_one h1
  rw [← hi]
  exact Subring.pow_mem _ hz i

set_option maxHeartbeats 4000000 in

theorem smul_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hvac⟩ := hP
  have hψ : IsStdChar D ψ (-1) := hvac.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW).1
  set Λ := latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True with hΛ
  obtain ⟨K, g, hgΛ, hgen⟩ := gens D V W ΛV ΛW hSV.1.fg hSW.1.fg
  refine ⟨K, fun M e P O Φ φ hM _ he _ hz hlev hO hθ => ?_⟩
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hoe := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hoc := hoe.conj
  have hee : e * e = e := hoe.idem
  have hcc : cA D e * cA D e = cA D e := hoc.idem
  have half' : ∀ {a : AE D} {u : WO V W}, IsHalf a u ↔ a • u = u := fun {a u} =>
    (GlobalTheory.PlaceModel.isHalf_iff V W).trans (GlobalTheory.PlaceModel.mem_half V W)
  let r : AE D := algebraMap D.host.F (AE D) ((M : D.host.F)⁻¹)
  have hrk : r * (M : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) M, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one]
  have hcr : cA D r = r := by
    have h1 : cA D r * (M : AE D) = 1 := by rw [← map_natCast (cA D) M, ← map_mul, hrk, map_one]
    calc cA D r = cA D r * ((M : AE D) * r) := by rw [mul_comm (M : AE D) r, hrk, mul_one]
      _ = r := by rw [← mul_assoc, h1, one_mul]
  have hnat : ∀ z : WO V W, M • z = (M : AE D) • z := fun z => (Nat.cast_smul_eq_nsmul (AE D) M z).symm
  have hkrz : ∀ z : WO V W, M • (r • z) = z := fun z => by rw [hnat, smul_smul, mul_comm, hrk, one_smul]
  let h : Fin K → WO V W := fun i => r • (e • g i)
  let y : (Fin K → Fin M) → WO V W := fun c => ∑ i, (c i : ℕ) • h i
  have heh : ∀ i, e • h i = h i := fun i => by
    simp only [h]; rw [smul_comm e r, smul_smul e e, hee]
  have hye : ∀ c, IsHalf e (y c) := fun c => half'.2 (by
    simp only [y]; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, heh])
  have hMh : ∀ i, M • h i = e • g i := fun i => hkrz _
  have heg : ∀ i, e • g i ∈ Λ := fun i => GlobalTheory.PlaceModelSum.idem_smul_latO hee (hgΛ i)
  have hMy : ∀ c, M • y c ∈ Λ := fun c => by
    simp only [y]; rw [Finset.smul_sum]
    exact sum_mem fun i _ => by rw [smul_comm, hMh]; exact AddSubgroup.nsmul_mem _ (heg i) _

  have hprod : ∀ t c, ψ (symplO V W t (y c)) = ∏ i, ψ (symplO V W t (h i)) ^ (c i : ℕ) := fun t c => by
    let F := AddMonoidHom.mk' (symplO V W t) (GlobalTheory.PlaceModel.symplO_add_right V W t)
    change ψ (F (y c)) = ∏ i, ψ (F (h i)) ^ (c i : ℕ)
    simp only [y, map_sum, map_nsmul, char_sum, AddChar.map_nsmul_eq_pow]
  have hroot : ∀ t ∈ Λ, ∀ i, ψ (symplO V W t (h i)) ^ M = 1 := fun t ht i =>
    (root_mem hψ hSV hSW hM (O := ⊤) (Subring.mem_top _) ht (by rw [hMh]; exact heg i)).1

  have hdualT : ∀ t ∈ Λ, IsHalf (cA D e) t → (∀ i, ψ (symplO V W t (h i)) = 1) →
      ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u := by
    intro t ht hth hall
    have hx : r • t ∈ GlobalTheory.PlaceModel.half V W (cA D e) := by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, half'.1 hth]
    have hmem := hoc.mem_of_dual hdual (r • t) hx (fun z hz => by
      obtain ⟨hzΛ, hzh⟩ := AddSubgroup.mem_inf.1 hz
      rw [GlobalTheory.LatVac.cA_cA, GlobalTheory.PlaceModel.mem_half] at hzh
      obtain ⟨n, u, hu, hzn⟩ := hgen M hMpos z hzΛ
      let ρ : WO V W →+ WO V W :=
        (DistribMulAction.toAddMonoidHom _ r).comp (DistribMulAction.toAddMonoidHom _ e)
      have hρ : r • z = ∑ i, n i • h i + e • u := by
        have e1 : r • z = ρ z := by
          simp only [ρ, AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply, hzh]
        rw [e1, hzn, map_add, map_sum, map_nsmul]
        simp only [map_zsmul]
        congr 1
        exact hkrz (e • u)
      rw [GlobalTheory.PlaceModel.symplO_smul, hcr, hρ]
      let F := AddMonoidHom.mk' (symplO V W t) (GlobalTheory.PlaceModel.symplO_add_right V W t)
      change ψ (F _) = 1
      rw [map_add, AddChar.map_add_eq_mul, map_sum, char_sum]
      simp only [map_zsmul, AddChar.map_zsmul_eq_zpow]
      change (∏ i, ψ (symplO V W t (h i)) ^ n i) * ψ (symplO V W t (e • u)) = 1
      rw [Finset.prod_eq_one fun i _ => by rw [hall i, _root_.one_zpow], one_mul]
      exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW ht (GlobalTheory.PlaceModelSum.idem_smul_latO hee hu))
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hmem
    exact ⟨r • t, h1, (GlobalTheory.PlaceModel.isHalf_iff V W).2 h2, (hkrz t).symm⟩
  have hconv : ∀ u ∈ Λ, ∀ i, ψ (symplO V W (M • u) (h i)) = 1 := fun u hu i => by
    have a1 : symplO V W (M • u) (h i) = M • symplO V W u (h i) :=
      (AddMonoidHom.mk' (fun x => symplO V W x (h i)) fun x x' =>
        GlobalTheory.PlaceModel.symplO_add_left V W x x' _).map_nsmul M u
    have a2 : symplO V W u (M • h i) = M • symplO V W u (h i) :=
      (AddMonoidHom.mk' (symplO V W u) (GlobalTheory.PlaceModel.symplO_add_right V W u)).map_nsmul M (h i)
    rw [a1, ← a2, hMh]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW hu (heg i)

  have hA : ∀ t ∈ Λ, IsHalf (cA D e) t → ∑ c, ψ (symplO V W t (y c)) =
      if ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u then (M : ℂ) ^ K else 0 := by
    intro t ht hth
    simp only [hprod t]
    rw [charSum M K hM _ (hroot t ht)]
    by_cases hc : ∃ u ∈ Λ, IsHalf (cA D e) u ∧ t = M • u
    · rw [if_pos hc, if_pos]
      obtain ⟨u, hu, -, rfl⟩ := hc
      exact hconv u hu
    · rw [if_neg hc, if_neg]
      exact fun hall => hc (hdualT t ht hth hall)

  obtain ⟨C, hCh, hC⟩ := GlobalTheory.BadOrth.finCosets D V W ΛV ΛW hSV hSW (cA D e) hcc M hMpos
  let L : AddSubgroup (WO V W) :=
    AddSubgroup.map (nsmulAddMonoidHom M) (Λ ⊓ GlobalTheory.PlaceModel.half V W (cA D e))
  have memL : ∀ x, x ∈ L ↔ ∃ u ∈ Λ, IsHalf (cA D e) u ∧ x = M • u := fun x => by
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hx
      exact ⟨u, (AddSubgroup.mem_inf.1 hu).1, (GlobalTheory.PlaceModel.isHalf_iff V W).2 (AddSubgroup.mem_inf.1 hu).2, rfl⟩
    · rintro ⟨u, hu, hue, rfl⟩
      exact AddSubgroup.mem_map.2 ⟨u, AddSubgroup.mem_inf.2 ⟨hu, (GlobalTheory.PlaceModel.isHalf_iff V W).1 hue⟩, rfl⟩
  let mkL : WO V W → WO V W ⧸ L := QuotientAddGroup.mk
  have hmkL : ∀ a b, mkL a = mkL b ↔ a - b ∈ L := fun a b => by
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  let C' := C.filter (· ∈ Λ)
  let Q : Finset (WO V W ⧸ L) := C'.image mkL
  have hrepex : ∀ q ∈ Q, ∃ c ∈ C', mkL c = q := fun q hq => Finset.mem_image.1 hq
  let rep : WO V W ⧸ L → WO V W := fun q => if hq : q ∈ Q then (hrepex q hq).choose else 0
  have hrep : ∀ q ∈ Q, rep q ∈ Λ ∧ IsHalf (cA D e) (rep q) ∧ mkL (rep q) = q := fun q hq => by
    simp only [rep, dif_pos hq]
    obtain ⟨h1, h2⟩ := (hrepex q hq).choose_spec
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
    exact ⟨h4, hCh _ h3, h2⟩
  have hcover : ∀ t ∈ Λ, IsHalf (cA D e) t → mkL t ∈ Q := fun t ht hth => by
    obtain ⟨c, hc, u, hu, hue, htc⟩ := hC t hth (AddSubgroup.nsmul_mem _ ht M)
    have hcΛ : c ∈ Λ := by
      rw [show c = t - M • u by rw [htc]; abel]
      exact sub_mem ht (AddSubgroup.nsmul_mem _ hu M)
    refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hc, hcΛ⟩, (hmkL c t).2 ?_⟩
    rw [htc, show c - (c + M • u) = M • (-u) by rw [smul_neg]; abel]
    exact AddSubgroup.mem_map.2 ⟨-u, AddSubgroup.mem_inf.2 ⟨neg_mem hu, neg_mem ((GlobalTheory.PlaceModel.isHalf_iff V W).1 hue)⟩, rfl⟩

  let a : (Fin K → Fin M) → ℂ := fun c =>
    ((M : ℂ) ^ K)⁻¹ * ∑ q ∈ Q, Φ (rep q) * ψ (symplO V W (-(rep q)) (y c))
  have hMK : ((M : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hM)
  have hΦ : ∀ t, Φ t = halfInd (cA D e) Λ t * ∑ c, a c * ψ (symplO V W t (y c)) := by
    intro t
    rw [halfInd]
    split_ifs with ht
    · rw [one_mul]
      have hsub : ∀ q c, ψ (symplO V W (t - rep q) (y c)) =
          ψ (symplO V W (-(rep q)) (y c)) * ψ (symplO V W t (y c)) := fun q c => by
        rw [sub_eq_add_neg, add_comm, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
      have e1 : ∑ c, a c * ψ (symplO V W t (y c)) =
          ((M : ℂ) ^ K)⁻¹ * ∑ q ∈ Q, Φ (rep q) * ∑ c, ψ (symplO V W (t - rep q) (y c)) := by
        simp only [a, hsub, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => by ring
      have e2 : ∀ q ∈ Q, ∑ c, ψ (symplO V W (t - rep q) (y c)) = if mkL t = q then (M : ℂ) ^ K else 0 :=
        fun q hq => by
          obtain ⟨hq1, hq2, hq3⟩ := hrep q hq
          rw [hA _ (sub_mem ht.1 hq1) (half'.2 (by rw [smul_sub, half'.1 ht.2, half'.1 hq2]))]
          refine if_congr ?_ rfl rfl
          rw [← memL, ← hmkL, hq3]
      rw [e1, Finset.sum_congr rfl fun q hq => by rw [e2 q hq, mul_ite, mul_zero], Finset.sum_ite_eq,
        if_pos (hcover t ht.1 ht.2)]
      obtain ⟨-, -, hr3⟩ := hrep (mkL t) (hcover t ht.1 ht.2)
      obtain ⟨w, hw, hwh, hwe⟩ := (memL _).1 ((hmkL _ _).1 hr3)
      have hΦr : Φ (rep (mkL t)) = Φ t := by
        rw [show rep (mkL t) = t + M • w by rw [← hwe]; abel]
        exact hlev.2 w hw hwh t
      rw [hΦr, mul_comm (Φ t), ← mul_assoc, inv_mul_cancel₀ hMK, one_mul]
    · rw [zero_mul]
      by_contra h0
      exact ht ⟨(hlev.1 t h0).1, (hlev.1 t h0).2⟩
  have hY : ∀ c, IsHalf (cA D (cA D e)) (y c) := fun c => by rw [GlobalTheory.LatVac.cA_cA]; exact hye c
  have hφ := GlobalTheory.DatumFourier.thetaAt_eq_sum y a hθ hY hΦ
  have hb : ∀ c, (∑ q ∈ Q, Φ (rep q) * ψ (symplO V W (-(rep q)) (y c))) ∈ O := fun c =>
    sum_mem fun q hq => mul_mem (hO _) (root_mem hψ hSV hSW hM hz (neg_mem (hrep q hq).1) (hMy c)).2
  rw [hφ, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  have e2 : ((M : ℂ) ^ K) • (a c • heisO ψ V W (y c) f₀) = (⟨_, hb c⟩ : O) • heisO ψ V W (y c) f₀ := by
    rw [smul_smul, Subring.smul_def]
    congr 1
    simp only [a]
    rw [← mul_assoc, mul_inv_cancel₀ hMK, one_mul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y c, hye c, hMy c, rfl⟩)

end GlobalTheory.LevelFourier

end
