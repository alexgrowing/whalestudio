import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

open scoped GlobalTheory.VacAny
open Topology

noncomputable section
namespace GlobalTheory.VacAvg

def schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) : Module.End ℂ ((κ → K) → ℂ) where
  toFun := schr ψ z
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' r f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schrL_apply {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) (f : (κ → K) → ℂ) : schrL ψ z f = schr ψ z f := rfl

theorem ops_schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ] :
    GlobalTheory.Published.SvN.Ops (fun z z' : (κ → K) × (κ → K) => ψ (⅟(2 : K) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))) (schrL ψ) where
  zero v := by funext x; simp [schrL_apply, schr]
  mul x y v := by simp only [schrL_apply]; exact schr_schr ψ x y v

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (t : A) : ψ t ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem eventually_schr_fix {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] {f : (κ → Fv F v) → ℂ} (hf : f ∈ SB (κ → Fv F v)) :
    ∀ᶠ z in 𝓝 (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ z f = f := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  obtain ⟨K, hK⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hf
  have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
      z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h1 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, ∀ x ∈ tsupport f,
      x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v)) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2
      (P := fun (z : (κ → Fv F v) × (κ → Fv F v)) (x : κ → Fv F v) =>
        x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v))) fun x _ => ?_
    refine (U₀.isOpen.preimage hc).mem_nhds ?_
    simpa using U₀.zero_mem
  have h2 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, z.1 ∈ (K : Set (κ → Fv F v)) :=
    (K.isOpen.preimage continuous_fst).mem_nhds K.zero_mem
  filter_upwards [h1, h2] with z hz1 hz2
  funext x
  show ψ (x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2)) * f (x + z.1) = f x
  rw [hK z.1 hz2 x]
  by_cases hx : x ∈ tsupport f
  · rw [hU₀ _ (hz1 x hx), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tens_sum {F : Type} [Field F] [NumberField F] {R κ ι : Type} (ev : AF F → R) (s : Finset ι) (c : ι → ℂ)
    (g : ι → (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (∑ q ∈ s, c q • g q) r = ∑ q ∈ s, c q • tens ev (g q) r := by
  funext x
  simp only [tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem rho_sum {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ ι : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (γ : W) (s : Finset ι)
    (Φ : ι → (κ → R) → ℂ) : d.rho ψ γ (∑ q ∈ s, Φ q) = ∑ q ∈ s, d.rho ψ γ (Φ q) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem avg_eigen : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl F) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT w Ψ _ hyp m f φ hSB hstd hsum
  classical
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ w) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 w
  obtain ⟨hvSB, hv0, θ, -, hθ⟩ := hT.geo.hM'.vac w
  have hat : ∀ γ ∈ latAtV G.V' G.W w, At (evFin F w) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1
  set L := schrL (κ := Fin a' × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ w) with hL
  set vac := G.M'.vac w with hvac
  set Λ := (latAtV G.V' G.W w).map (GlobalTheory.LatVac.locCo G.M'.co w) with hΛ
  obtain ⟨-, hΛc⟩ := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat w
  have hAct : ∀ γ ∈ latAtV G.V' G.W w, ∀ φ₀ : (Fin a' × Fin (a + a') → Fv F w) → ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) φ₀ (L (GlobalTheory.LatVac.locCo G.M'.co w γ) φ₀) :=
    fun γ hγ φ₀ => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ w γ (hat γ hγ) φ₀
  have huniq : ∀ γ ∈ latAtV G.V' G.W w, ∀ c₀ : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) vac (c₀ • vac) →
      L (GlobalTheory.LatVac.locCo G.M'.co w γ) vac = c₀ • vac := fun γ hγ c₀ h =>
    GlobalTheory.TensUniq.eq_of_tens_eq w vac _ _ hvSB fun r hr => (hAct γ hγ vac r hr).symm.trans (h r hr)
  have hinj : ∀ e e' : ℂ, e • vac = e' • vac → e = e' := fun e e' h => smul_left_injective ℂ hv0 h
  have hex : ∀ z ∈ Λ, ∃ e : ℂ, L z vac = e • vac := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨_, huniq γ hγ _ (hθ γ hγ)⟩
  let α : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z => if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1
  have hαspec : ∀ z, (∃ e : ℂ, L z vac = e • vac) → L z vac = α z • vac := fun z h => by
    show _ = (if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1) • vac
    rw [dif_pos h]
    exact h.choose_spec
  let c : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) →
      (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z z' => GlobalTheory.LatVac.psiAt B.ψ w (⅟(2 : Fv F w) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))
  have hops : GlobalTheory.Published.SvN.Ops c L := ops_schrL _
  have hαne : ∀ z ∈ Λ, α z ≠ 0 := by
    intro z hz h0
    have h1 := hops.mul (-z) z vac
    rw [hαspec z (hex z hz), h0, zero_smul, map_zero, neg_add_cancel, hops.zero] at h1
    exact hv0 ((smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero _ _))
  have hsplit : GlobalTheory.Published.SvN.Splits c Λ α := by
    refine ⟨hαne, fun x hx y hy => hinj _ _ ?_⟩
    have h1 := hops.mul x y vac
    rw [hαspec y (hex y hy), map_smul, hαspec x (hex x hx), hαspec (x + y) (hex _ (Λ.add_mem hx hy)), smul_smul,
      smul_smul] at h1
    rw [mul_comm (α x)]
    exact h1
  have hfix : ∀ᶠ z in 𝓝 (0 : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w)),
      L z vac = vac ∧ ∀ i, L z (φ i w) = φ i w :=
    (eventually_schr_fix w _ hψc hvSB).and (Filter.eventually_all.2 fun i => eventually_schr_fix w _ hψc (hSB i w))
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hfix
  have hUα : ∀ u ∈ U.toAddSubgroup, α u = 1 := fun u hu =>
    hinj _ _ (by rw [← hαspec u ⟨1, by rw [one_smul]; exact (hU hu).1⟩, one_smul]; exact (hU hu).1)
  have hfin : Finite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) :=
    GlobalTheory.Published.SvN.finite_quot Λ U.toAddSubgroup U.mem_nhds_zero hΛc subset_rfl
  letI := Fintype.ofFinite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ)
  obtain ⟨avg, havg⟩ : ∃ avg : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, ∀ i,
      avg i = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • L q.out.1 (φ i w) := ⟨_, fun _ => rfl⟩
  have heig : ∀ i, ∀ z ∈ Λ, L z (avg i) = α z • avg i := fun i z hz => by
    rw [havg i]
    exact GlobalTheory.Published.SvN.average hops hsplit U.toAddSubgroup hUα (φ i w) (fun u hu => (hU hu).2 i) z hz
  set N := Fintype.card (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) with hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  choose γq hγq hγqe using fun q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ => AddSubgroup.mem_map.1 q.out.2
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor w (f i) (φ i) (hstd i)
  have hpure : ∀ i, pure (f i) (φ i) = tens (evFin F w) (φ i w) (r i) := fun i => by
    rw [hr2, Function.update_eq_self]
  have hRest : ∀ i, Rest (evFin F w) (φ i w) (r i) := fun i =>
    ⟨hr1 i, hpure i ▸ GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hSB i) (hstd i)⟩
  have hΨ' : Ψ = ∑ i, tens (evFin F w) (φ i w) (r i) := by
    rw [hsum]; exact Finset.sum_congr rfl fun i _ => hpure i
  have hqΨ : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, G.M'.co.rho B.ψ (γq q) Ψ = α q.out.1 • Ψ := fun q =>
    hyp _ (hγq q) _ (by
      have := hAct _ (hγq q) vac
      rwa [hγqe q, hαspec _ (hex _ q.out.2)] at this)
  have hqΨ2 : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ,
      G.M'.co.rho B.ψ (γq q) Ψ = ∑ i, tens (evFin F w) (L q.out.1 (φ i w)) (r i) := fun q => by
    rw [hΨ', rho_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAct _ (hγq q) (φ i w) (r i) (hRest i), hγqe q]
  have e1 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ = (N : ℂ) • Ψ := by
    calc ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ
          = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, Ψ :=
          Finset.sum_congr rfl fun q _ => by rw [hqΨ q, smul_smul, inv_mul_cancel₀ (hαne _ q.out.2), one_smul]
      _ = (N : ℂ) • Ψ := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ =
      ∑ i, tens (evFin F w) (avg i) (r i) := by
    simp only [hqΨ2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [havg i, tens_sum]
  have hgSB : ∀ i, (N : ℂ)⁻¹ • avg i ∈ SB (Fin a' × Fin (a + a') → Fv F w) := fun i => by
    rw [havg i]
    exact (SB _).smul_mem _ (Submodule.sum_mem _ fun q _ => (SB _).smul_mem _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 w _ _ (hSB i w)))
  refine ⟨fun i => (N : ℂ)⁻¹ • avg i, hgSB, fun i γ hγ c₀ hc => ?_, ?_⟩
  · have hz : GlobalTheory.LatVac.locCo G.M'.co w γ ∈ Λ := AddSubgroup.mem_map_of_mem _ hγ
    have e := huniq γ hγ c₀ hc
    rw [hαspec _ (hex _ hz)] at e
    have hc₀ := hinj _ _ e
    have := hAct γ hγ ((N : ℂ)⁻¹ • avg i)
    rwa [map_smul, heig i _ hz, hc₀, smul_comm] at this
  · calc Ψ = (N : ℂ)⁻¹ • ((N : ℂ) • Ψ) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
      _ = _ := by
        rw [← e1, e2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← tens_smul, hr2]

end GlobalTheory.VacAvg
