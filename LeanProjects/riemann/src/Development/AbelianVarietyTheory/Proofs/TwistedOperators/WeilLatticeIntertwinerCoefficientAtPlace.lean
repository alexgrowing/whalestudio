import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatCoef

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts GlobalTheory.FinWeilO

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem map_eq_zero_of_local_vacuum {N : Type} [AddCommGroup N] [Module ℂ N] (h : IsHeis σ w γ W) (A : Submodule R X)
    (hA : SelfDual γ A) (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (L : M →ₗ[ℂ] N)
    (hL : ∀ x e, Fixes W A e → P x ∈ A → L (W x e) = 0) (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : L m = 0 := by
  classical
  have hsm : ∀ (c : ℂ) e, Fixes W A e → Fixes W A (c • e) := fun c e he a ha => by rw [map_smul, he a ha]
  have key : ∀ {ι : Type} (x : ι → X) (s : Finset ι) (e : ι → M), (∀ i, Fixes W A (e i)) →
      (∀ a ∈ A, W (P a) (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i)) →
      L (∑ i ∈ s, W (x i) (e i)) = 0 := by
    intro ι x s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro e he hfix
      by_cases hall : ∀ i ∈ s, P (x i) ∈ A
      · rw [map_sum]
        exact Finset.sum_eq_zero fun i hi => hL _ _ (he i) (hall i hi)
      · push Not at hall
        obtain ⟨j, hj, hjA⟩ := hall
        rw [hA] at hjA
        push Not at hjA
        obtain ⟨a, ha, hz⟩ := hjA
        have hz' : γ (P a) (x j) ≠ 1 := by
          intro h0
          rw [hP] at h0
          exact hz (h.swap_eq_one h0)
        set z := γ (P a) (x j) with hzdef
        have hact : ∀ i, W (P a) (W (x i) (e i)) = γ (P a) (x i) • W (x i) (e i) := fun i => by
          rw [h.comm, he i _ (hPA a ha)]
        have hsum : (1 - z) • ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s.erase j, W (x i) ((γ (P a) (x i) - z) • e i) := by
          rw [Finset.sum_erase s (by simp [hzdef]), sub_smul, one_smul]
          have h4 : ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) := by
            rw [← hfix a ha, map_sum]
            exact Finset.sum_congr rfl fun i _ => hact i
          calc _ = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) - ∑ i ∈ s, z • W (x i) (e i) := by
                rw [← h4, Finset.smul_sum]
            _ = _ := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sub_smul]
        have h3 := ih (s.erase j) (Finset.erase_ssubset hj) (fun i => (γ (P a) (x i) - z) • e i)
          (fun i => hsm _ _ (he i)) (fun b hb => by rw [← hsum, map_smul, hfix b hb])
        rw [← hsum, map_smul] at h3
        exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hz'.symm)
  have hmem : m ∈ Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} := by rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  choose x e he hge using fun i => (g i).2
  have hm' : m = ∑ i, W (x i) (c i • e i) := by
    rw [← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hge i]
  rw [hm'] at hm ⊢
  exact key x Finset.univ _ (fun i => hsm _ _ (he i)) hm

theorem intertwiner_eq_sum (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (P : X →ₗ[R] X) (hP : ∀ x y, γ (P x) y = γ x (P y))
    (hPA : ∀ a ∈ A, P a ∈ A) (hPP : ∀ x, P (P x) = P x) (hφ : ∀ x, φ (x - P x) = x - P x) {ι : Type} [Fintype ι]
    (c : ℂ) (b : ι → X) (hb : ∀ i, P (b i) = b i) (hTe : ∀ e, Fixes W A e → T e = c • ∑ i, W (b i) e) (m : M)
    (hm : ∀ a ∈ A, W (P a) m = m) : T m = c • ∑ i, W (b i) m := by
  let Q : M →ₗ[ℂ] M := c • ∑ i, W (b i)
  have hQ : ∀ v, Q v = c • ∑ i, W (b i) v := fun v => by simp [Q, LinearMap.sum_apply]
  have key := map_eq_zero_of_local_vacuum h A hA hspan P hP hPA (T - Q) (fun x e he hx => ?_) m hm
  · rwa [LinearMap.sub_apply, hQ, sub_eq_zero] at key
  obtain ⟨y, hy⟩ : ∃ y, y = x - P x := ⟨_, rfl⟩
  have hPy : P y = 0 := by rw [hy, map_sub, hPP, sub_self]
  have h1 : W y e = γ (w • y) (P x) • W x e := by
    have h2 := h.comp y (P x) e
    rwa [he _ hx, hy, sub_add_cancel, ← hy] at h2
  have hcomm : ∀ i, W y (W (b i) e) = W (b i) (W y e) := fun i => by
    have h2 : γ y (b i) = 1 := by rw [← hb i, ← hP, hPy, h.zero_left]
    rw [h.comm, h2, one_smul]
  have h3 : T (W y e) = Q (W y e) := by
    rw [hT, hy, hφ, ← hy, hTe e he, hQ, map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hcomm i
  rw [h1, map_smul, map_smul] at h3
  rw [LinearMap.sub_apply, sub_eq_zero]
  exact smul_right_injective M (h.ne_zero _ _) h3

theorem coef_of_local_vacuum (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X)
    (hB : SelfDual γ (A.map φ)) (hi : idx A (A.map φ) ≠ 0) (T : M →ₗ[ℂ] M) (hT : ∀ x v, T (W x v) = W (φ x) (T v))
    (hTe : ∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) (P : X →ₗ[R] X) (hP : ∀ x y, γ (P x) y = γ x (P y))
    (hPA : ∀ a ∈ A, P a ∈ A) (hPP : ∀ x, P (P x) = P x) (hφ : ∀ x, φ (x - P x) = x - P x)
    (hφP : ∀ x, φ (P x) = P (φ x)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ∀ a ∈ A, ∀ g, ℓ (W (P a) g) = ℓ g) (m : M)
    (hm : ∀ a ∈ A, W (P a) m = m) : ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * ℓ m := by
  classical
  obtain ⟨n, t, ht, hu⟩ := exists_transversal_of_idx_ne_zero A _ hi
  have hBP : ∀ x ∈ A.map φ, P x ∈ A.map φ ∧ x - P x ∈ A := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨⟨P a, hPA a ha, hφP a⟩, ?_⟩
    rw [← hφP, ← map_sub, hφ]
    exact A.sub_mem ha (hPA a ha)
  obtain ⟨b, hbdef⟩ : ∃ b : Fin n → X, ∀ i, b i = P (t i) := ⟨_, fun _ => rfl⟩
  have hb : ∀ i, P (b i) = b i := fun i => by rw [hbdef, hPP]
  have hbB : ∀ i, b i ∈ A.map φ := fun i => by rw [hbdef]; exact (hBP _ (ht i)).1
  have hd : ∀ j, t j - b j ∈ A := fun j => by rw [hbdef]; exact (hBP _ (ht j)).2
  have hbu : ∀ y ∈ A.map φ, ∃! i, y - b i ∈ A := by
    intro y hy
    obtain ⟨i, hi1, hi2⟩ := hu y hy
    refine ⟨i, ?_, fun j hj => hi2 j ?_⟩
    · have h1 := A.add_mem hi1 (hd i)
      rwa [sub_add_sub_cancel] at h1
    · have h1 := A.sub_mem hj (hd j)
      rwa [sub_sub_sub_cancel_right] at h1
  have hTe' : ∀ e, Fixes W A e → T e = (lam (idx A (A.map φ)))⁻¹ • ∑ i, W (b i) e := fun e he => by
    rw [hTe e he, normOp, ((sumOp_transversal h A _ hB).1 e he (Fin n) b hbB hbu).1]
  rw [intertwiner_eq_sum h A hA hspan φ T hT P hP hPA hPP hφ _ b hb hTe' m hm, map_smul, map_sum, smul_eq_mul]
  congr 1
  obtain ⟨i₀, hi₀, hu₀⟩ := hbu 0 (Submodule.zero_mem _)
  have hbA : b i₀ ∈ A := by simpa using A.neg_mem hi₀
  rw [Finset.sum_eq_single i₀ (fun i _ hne => ?_) (fun h0 => absurd (Finset.mem_univ _) h0)]
  · have h1 := hm _ hbA
    rw [hb] at h1
    rw [h1]
  · have hbi : b i ∉ A := fun h1 => hne (hu₀ i (by simpa using A.neg_mem h1))
    rw [hA] at hbi
    push Not at hbi
    obtain ⟨a, ha, hz⟩ := hbi
    have hz' : γ (P a) (b i) ≠ 1 := fun h0 => by
      rw [hP, hb] at h0
      exact hz (h.swap_eq_one h0)
    have e1 : W (P a) (W (b i) m) = γ (P a) (b i) • W (b i) m := by rw [h.comm, hm a ha]
    have e2 := hℓ a ha (W (b i) m)
    rw [e1, map_smul, smul_eq_mul] at e2
    have e3 : (γ (P a) (b i) - 1) * ℓ (W (b i) m) = 0 := by rw [sub_mul, e2, one_mul, sub_self]
    exact (mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 hz')

end Abstract

section Concrete

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem placeIdem_mul_self {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hαα : α * α = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, one_mul]
    · rw [h0 w hw, mul_zero]
  exact Prod.ext (mul_zero _) hαα

theorem opF_mulF_fix {hψ : IsCharAF D.host.F ψ} {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ ΛS ΛT w lam Om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {f : thetaSub ψ S T}
    (hf : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f) {a : XF S T} (ha : a ∈ latF S T ΛS ΛT) :
    opF hψ S T w (mulF S T (algebraMap (AF D.host.F) (AE D) ε) a) f = f := by
  have H := isHeis_opF hψ S T h.hw
  obtain ⟨x, hxdef⟩ : ∃ x, x = mulF S T (algebraMap (AF D.host.F) (AE D) ε) a := ⟨_, rfl⟩
  rw [← hxdef]
  have hu : (x : WO S T) ∈ latO S T ΛS ΛT fun u => u = v := by
    rw [hxdef, coe_mulF]
    exact GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha
  have hxA : x ∈ latF S T ΛS ΛT := GlobalTheory.PlaceModel.latO_le_top _ hu
  have hεx := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  by_cases hs : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, he2⟩ := hs
    have hhalf : ∀ e', IsSplitIdem D e' → mulF S T e' x ∈ latF S T ΛS ΛT ∧ opF hψ S T w (mulF S T e' x) f = f := by
      intro e' he'
      have h1 : e' • (x : WO S T) ∈ latO S T ΛS ΛT fun _ => True := idem_smul_mem he'.1 _ hxA
      have h2 : e' • (x : WO S T) ∈ latO S T ΛS ΛT fun u => u = v := by
        have h3 := GlobalTheory.PlaceModel.placeIdem_smul_mem hε h1
        rwa [smul_comm, hεx] at h3
      refine ⟨h1, Subtype.ext ?_⟩
      rw [coe_opF, phase_half he' w (isHalf_smul he'.1 _), one_smul, coe_mulF]
      exact hf.2 e' he' _ h2 (isHalf_smul he'.1 _)
    have he' := isSplitIdem_conj he
    have hx : x = mulF S T e x + mulF S T (cA D e) x := XF.ext (by
      rw [XF.coe_add, coe_mulF, coe_mulF, ← add_smul, he2, hεx])
    rw [hx, ← H.comp_of_mem h.sd (hhalf e he).1 (hhalf _ he').1, (hhalf _ he').2, (hhalf e he).2]
  · obtain ⟨b, hb, hb2⟩ := exists_half_of_nonSplit (⟨hε, hs⟩ : NonSplitAt D v ε)
    have h1 : 2 • (b • x) = x := XF.ext (by
      show 2 • (b • (x : WO S T)) = x
      rw [two_nsmul, ← add_smul, ← two_mul, hb2, hεx])
    have h2 : b • (x : WO S T) ∈ latO S T ΛS ΛT fun u => u = v :=
      GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ hu
    have h3 : b • x ∈ latF S T ΛS ΛT := GlobalTheory.PlaceModel.latO_le_top _ h2
    apply Subtype.ext
    rw [coe_opF]
    nth_rewrite 1 [← h1]
    rw [phase_two h.sd w h3, one_smul, ← h1, XF.coe_nsmul]
    exact hf.1 _ h2

end Concrete

end GlobalTheory.LatCoef

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts GlobalTheory.FinWeilO in

theorem GlobalTheory.LatCoef.latCoef : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv T v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → l2 μ 𝓕 (Om (1, embV T v a) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v a)))))⁻¹ * l2 μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  intro D ψ S T hψ lam w₀ Om h μ 𝓕 hμ v a f₁ f₂ h₁ h₂
  obtain ⟨η, hηdef⟩ : ∃ η : AF D.host.F, η = pairA D.host.F 0 (singleV D.host.F v 1) := ⟨_, rfl⟩
  have hε : IsPlaceIdem D v η := hηdef ▸
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hg : SuppPl η S (1 : GA D S) := fun i j => by rw [mt_one, sub_self]; simp
  have hk : SuppPl η T (embV T v a) := hηdef ▸ GlobalTheory.PlaceTensor.suppPl_emb T v a
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have H := isHeis_opF hψ.1 S T h.hw
  have hphase : ∀ x : XF S T, phase ψ w₀ x * (starRingEnd ℂ) (phase ψ w₀ x) = 1 := fun x => by
    rw [Complex.mul_conj', show ‖phase ψ w₀ x‖ = 1 from hψ.1.2.1 _]; simp
  have laws := fun g : thetaSub ψ S T => GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2
  let ℓ : thetaSub ψ S T →ₗ[ℂ] ℂ :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
      map_add' := fun g g' => ((laws g).2.2.2.1 g' g'.2).1
      map_smul' := fun c g => ((laws g).2.2.1 c).1 }
  have hℓ : ∀ a' ∈ latF S T (frameLat S) (frameLat T), ∀ g,
      ℓ (opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') g) = ℓ g := by
    intro a' ha' g
    obtain ⟨x, hx⟩ : ∃ x, x = mulF S T (algebraMap (AF D.host.F) (AE D) η) a' := ⟨_, rfl⟩
    have hfix := opF_mulF_fix h hε h₂.2 ha'
    rw [← hx] at hfix ⊢
    have hg' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin g.2
    have hf' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin f₂.2
    have l2' := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ hg' hf'
    have l3 := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ ((thetaSub ψ S T).smul_mem (phase ψ w₀ x) hg') hf'
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (opF hψ.1 S T w₀ x g : WO S T → ℂ) f₂ = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
    conv_lhs => rw [← hfix]
    rw [coe_opF, coe_opF, (l3.2.2.1 (phase ψ w₀ x)).2, (l2'.2.2.1 (phase ψ w₀ x)).1,
      ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2).2.2.2.2.2.2.1 x).1, ← mul_assoc, mul_comm (starRingEnd ℂ _),
      hphase, one_mul]
  have hm : ∀ a' ∈ latF S T (frameLat S) (frameLat T),
      opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') f₁ = f₁ := fun a' ha' =>
    opF_mulF_fix h hε h₁.2 ha'
  exact coef_of_local_vacuum H lam _ h.sd h.span (rhoF S T (1, embV T v a)) (h.sd' _) (h.fin _) (Om (1, embV T v a)) (h.op _)
    (h.vac _) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap])
    (fun a' ha' => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hε) _ ha')
    (fun x => XF.ext (by
      rw [coe_mulF, coe_mulF, smul_smul, ← map_mul, placeIdem_mul_self hε]))
    (fun x => XF.ext (by
      have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
          (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
        rw [sub_smul, one_smul]; rfl
      rw [coe_rhoF, e1, actO_smul, hoff]))
    (fun x => XF.ext (actO_smul _ _ _ _)) ℓ hℓ f₁ hm

end
