import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

open NumberField GlobalTheory.AllWt Module Matrix

noncomputable section

namespace GlobalTheory.SlopeGal

open GlobalTheory.SlopeExt

section Abstract

variable {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (ρ : V →+ E)

theorem exists_top_step {L : Submodule R V} (hL : Formalism.HN.IsLat ρ L) (h0 : L ≠ ⊥) :
    ∃ M : Submodule R V, M ≤ L ∧ M ≠ ⊥ ∧ Formalism.HN.deg ρ M = Formalism.HN.muMax ρ L * Formalism.HN.rk ρ M ∧
      ∀ N : Submodule R V, N ≤ L → Formalism.HN.muMax ρ L * Formalism.HN.rk ρ N ≤ Formalism.HN.deg ρ N → N ≤ M := by
  classical
  obtain ⟨h1, -, ⟨N₀, hN₀, hN₀', hs⟩, -⟩ := Formalism.HN.muChar R V E ρ L hL h0
  have hle := (h1 _).1 le_rfl
  obtain ⟨-, -, -, hrk, hbot, -⟩ := Formalism.HN.satBasic R V E ρ L hL
  set θ := Formalism.HN.muMax ρ L
  let S : Set (Submodule R V) := {N | N ≤ L ∧ θ * Formalism.HN.rk ρ N ≤ Formalism.HN.deg ρ N}
  obtain ⟨t, ht, hsup⟩ := Formalism.HN.finSup R V E ρ L S hL fun N hN => hN.1
  have hM : sSup S ∈ S := by
    rw [hsup]
    refine Finset.sup_induction (p := (· ∈ S)) ⟨bot_le, ?_⟩ (fun A hA B hB => ⟨sup_le hA.1 hB.1, ?_⟩)
      fun N hN => ht hN
    · rw [hbot, (hrk ⊥ bot_le).2 rfl]; simp
    · obtain ⟨e1, e2⟩ := Formalism.HN.degSupermod R V E ρ L A B hL hA.1 hB.1
      have e3 := hle (A ⊓ B) (inf_le_left.trans hA.1)
      have e4 : (Formalism.HN.rk ρ (A ⊔ B) : ℝ) = Formalism.HN.rk ρ A + Formalism.HN.rk ρ B - Formalism.HN.rk ρ (A ⊓ B) := by
        rw [eq_sub_iff_add_eq]; exact_mod_cast e1
      have := hA.2
      have := hB.2
      rw [e4]
      linarith
  refine ⟨sSup S, hM.1, fun h => hN₀' (le_bot_iff.1 (h ▸ le_sSup ⟨hN₀.1, ?_⟩)), le_antisymm (hle _ hM.1) hM.2,
    fun N hN h => le_sSup ⟨hN, h⟩⟩
  have : (Formalism.HN.rk ρ N₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hN₀' ((hrk N₀ hN₀.1).1 h)
  rw [← hs]
  exact (div_mul_cancel₀ _ this).le

theorem rk_deg_image (T : V →+ V) {A B : Submodule R V} (hA : Formalism.HN.IsLat ρ A) (hB : Formalism.HN.IsLat ρ B)
    (hAB : ∀ y, y ∈ B ↔ ∃ x ∈ A, T x = y) (hn : ∀ x ∈ A, ‖ρ (T x)‖ = ‖ρ x‖) :
    Formalism.HN.rk ρ B = Formalism.HN.rk ρ A ∧ Formalism.HN.deg ρ B = Formalism.HN.deg ρ A := by
  let f : A.toAddSubgroup →+ E := ρ.comp A.toAddSubgroup.subtype
  let g : A.toAddSubgroup →+ E := (ρ.comp T).comp A.toAddSubgroup.subtype
  have h1 : ∀ y, y ∈ Formalism.HN.zl ρ A ↔ ∃ m, f m = y :=
    fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩
  have h2 : ∀ y, y ∈ Formalism.HN.zl ρ B ↔ ∃ m, g m = y := fun y =>
    ⟨fun ⟨m, hm, e⟩ => by
      obtain ⟨x, hx, rfl⟩ := (hAB m).1 hm
      exact ⟨⟨x, hx⟩, e⟩, fun ⟨m, e⟩ => ⟨T m.1, (hAB _).2 ⟨m.1, m.2, rfl⟩, e⟩⟩
  have hn' : ∀ m, ‖f m‖ = ‖g m‖ := fun m => (hn m.1 m.2).symm
  haveI := hA.2
  haveI := hB.2
  refine ⟨?_, ?_⟩
  · have hf : Function.Injective f := fun x y h => Subtype.ext (hA.1 x.2 y.2 h)
    have hg : Function.Injective g := fun x y h =>
      hf (Formalism.HN.QuotientRealization.eq_of_norm_eq g f (fun m => (hn' m).symm) h)
    have e1 : Formalism.HN.zl ρ A = LinearMap.range f.toIntLinearMap := Submodule.ext h1
    have e2 : Formalism.HN.zl ρ B = LinearMap.range g.toIntLinearMap := Submodule.ext h2
    unfold Formalism.HN.rk Formalism.F.rk
    rw [e1, e2, ← (LinearEquiv.ofInjective f.toIntLinearMap hf).finrank_eq,
      ← (LinearEquiv.ofInjective g.toIntLinearMap hg).finrank_eq]
  · unfold Formalism.HN.deg Formalism.F.deg
    rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn']

end Abstract

section Fields

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem span_gal [IsGalois K K'] :
    Submodule.span K' (Set.range fun g : K' ≃ₐ[K] K' => (g.toLinearMap : K' →ₗ[K] K')) = ⊤ := by
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have h1 : LinearIndependent K' fun g : K' ≃ₐ[K] K' => (g.toLinearMap : K' →ₗ[K] K') :=
    (linearIndependent_toLinearMap K K' K').comp (fun g : K' ≃ₐ[K] K' => (g : K' →ₐ[K] K'))
      AlgEquiv.coe_algHom_injective
  refine h1.span_eq_top_of_card_eq_finrank' ?_
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Module.finrank_linearMap_self]

theorem exists_dual : ∃ (n : ℕ) (a : Fin n → 𝓞 K') (f : Fin n → K' →ₗ[K] K),
    (∀ i (r : 𝓞 K'), ∃ s : 𝓞 K, f i r = s) ∧ ∀ r : 𝓞 K', ∑ i, (a i : K') * algebraMap K K' (f i r) = r := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap :=
    by
      haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
      exact isLocalizedModule_iff_isLocalization.2 (IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K'))
  let f : Fin n → K' →ₗ[K] K := fun i => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
    (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap (Algebra.linearMap (𝓞 K) K) K (LinearMap.proj i ∘ₗ s)
  have hf : ∀ i (r : 𝓞 K'), f i r = (s r i : 𝓞 K) := fun i r =>
    IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap (Algebra.linearMap (𝓞 K) K)
      (LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => 𝓞 K) i ∘ₗ s) r
  refine ⟨n, fun i => p (Pi.single i 1), f, fun i r => ⟨_, hf i r⟩, fun r => ?_⟩
  have h1 : r = ∑ i, s r i • p (Pi.single i 1) := by
    conv_lhs => rw [← LinearMap.id_apply (R := 𝓞 K) r, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s r)]
    simp [map_sum]
  conv_rhs => rw [h1]
  simp only [hf]
  rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, mul_comm]
  rfl

end Fields

section Twist

variable {K K' V V' : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K' V'] {n : ℕ} (b : Basis (Fin n) K V) (ι : V →ₛₗ[algebraMap K K'] V')

theorem map_eq_sum (v : V) : ι v = ∑ k, algebraMap K K' (b.repr v k) • ι (b k) := by
  conv_lhs => rw [← b.sum_repr v, map_sum]
  simp only [map_smulₛₗ]

theorem exists_coord (h : LinearIndependent K' fun k => ι (b k)) :
    ∃ c : V' →ₗ[K'] Fin n → K', ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a := by
  obtain ⟨c, hc⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination K' fun k => ι (b k))
    (LinearMap.ker_eq_bot.2 h.fintypeLinearCombination_injective)
  exact ⟨c, fun a => LinearMap.congr_fun hc a⟩

variable (c : V' →ₗ[K'] Fin n → K')

def tw (φ : K' →ₗ[K] K') : V' →+ V' where
  toFun x := ∑ k, φ (c x k) • ι (b k)
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

def dn (f : K' →ₗ[K] K) : V' →+ V where
  toFun x := ∑ k, f (c x k) • b k
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem tw_apply (φ : K' →ₗ[K] K') (x : V') : tw b ι c φ x = ∑ k, φ (c x k) • ι (b k) := rfl

theorem map_dn (f : K' →ₗ[K] K) (x : V') : ι (dn b c f x) = tw b ι c (Algebra.linearMap K K' ∘ₗ f) x := by
  show ι (∑ k, f (c x k) • b k) = _
  rw [map_sum, tw_apply]
  simp only [map_smulₛₗ]
  rfl

theorem tw_smul (g : K' ≃ₐ[K] K') (a : K') (x : V') :
    tw b ι c g.toLinearMap (a • x) = g a • tw b ι c g.toLinearMap x := by
  simp [tw_apply, Finset.smul_sum, smul_smul]

variable {b ι c}

theorem dn_smul (hc : ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a) (f : K' →ₗ[K] K) (a : K') (v : V) :
    dn b c f (a • ι v) = f a • v := by
  show ∑ k, f (c (a • ι v) k) • b k = _
  rw [map_smul, map_eq_sum b ι v, hc]
  conv_rhs => rw [← b.sum_repr v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul, smul_smul, smul_eq_mul, mul_comm]

theorem tw_map (hc : ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a) (g : K' ≃ₐ[K] K') (v : V) :
    tw b ι c g.toLinearMap (ι v) = ι v := by
  rw [tw_apply]
  conv_lhs => rw [map_eq_sum b ι v, hc]
  conv_rhs => rw [map_eq_sum b ι v]
  simp

theorem tw_mem [NumberField K] [NumberField K'] [IsGalois K K'] {W : Submodule K' V'}
    (hW : ∀ (g : K' ≃ₐ[K] K'), ∀ x ∈ W, tw b ι c g.toLinearMap x ∈ W) (φ : K' →ₗ[K] K') {x : V'} (hx : x ∈ W) :
    tw b ι c φ x ∈ W := by
  have h : φ ∈ Submodule.span K' (Set.range fun g : K' ≃ₐ[K] K' => (g.toLinearMap : K' →ₗ[K] K')) :=
    span_gal K K' ▸ Submodule.mem_top
  induction h using Submodule.span_induction with
  | mem _ h => obtain ⟨g, rfl⟩ := h; exact hW g x hx
  | zero => simp [tw_apply]
  | add φ ψ _ _ h1 h2 => simpa [tw_apply, add_smul, Finset.sum_add_distrib] using W.add_mem h1 h2
  | smul a φ _ h1 => simpa [tw_apply, Finset.smul_sum, smul_smul] using W.smul_mem a h1

variable [NumberField K] [NumberField K'] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K') V']
  [IsScalarTower (𝓞 K') K' V']

theorem inf_eq_span [IsGalois K K'] (hc : ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a) {W : Submodule K' V'}
    (hW : ∀ (g : K' ≃ₐ[K] K'), ∀ x ∈ W, tw b ι c g.toLinearMap x ∈ W) (L : Submodule (𝓞 K) V) :
    Submodule.span (𝓞 K') (ι '' (L : Set V)) ⊓ W.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') (ι '' ((L ⊓ (W.comap ι).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · obtain ⟨m, a, f, hf, ha⟩ := exists_dual K K'
    have key : ∀ x ∈ Submodule.span (𝓞 K') (ι '' (L : Set V)),
        (∀ i, dn b c (f i) x ∈ L) ∧ ∑ i, a i • ι (dn b c (f i) x) = x := fun x hx => by
      induction hx using Submodule.closure_induction with
      | zero => simp
      | add x y _ _ h1 h2 =>
        refine ⟨fun i => by rw [map_add]; exact L.add_mem (h1.1 i) (h2.1 i), ?_⟩
        simp only [map_add, smul_add, Finset.sum_add_distrib, h1.2, h2.2]
      | smul_mem r x h =>
        obtain ⟨v, hv, rfl⟩ := h
        rw [← algebraMap_smul K' r]
        simp only [dn_smul hc]
        refine ⟨fun i => ?_, ?_⟩
        · obtain ⟨s, hs⟩ := hf i r
          rw [show f i (algebraMap (𝓞 K') K' r) = algebraMap (𝓞 K) K s from hs, algebraMap_smul]
          exact L.smul_mem s hv
        · conv_rhs => rw [show algebraMap (𝓞 K') K' r = _ from (ha r).symm, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smulₛₗ, ← algebraMap_smul K' (a i), smul_smul]
    rintro x ⟨hx, hxW⟩
    rw [← (key x hx).2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, ⟨(key x hx).1 i, ?_⟩, rfl⟩)
    show ι _ ∈ W
    rw [map_dn]
    exact tw_mem hW _ hxW
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, hv.2⟩

def twLat (g : K' ≃ₐ[K] K') (M : Submodule (𝓞 K') V') : Submodule (𝓞 K') V' where
  toAddSubmonoid := M.toAddSubmonoid.map (tw b ι c g.toLinearMap)
  smul_mem' := by
    rintro r _ ⟨x, hx, rfl⟩
    refine ⟨RingOfIntegers.mapRingHom (g.symm : K' →+* K') r • x, M.smul_mem _ hx, ?_⟩
    rw [← algebraMap_smul K', tw_smul, ← algebraMap_smul K' r]
    congr 1
    exact g.apply_symm_apply _

theorem tw_mem_span (hc : ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a) (g : K' ≃ₐ[K] K') (s : Set V) {x : V'}
    (hx : x ∈ Submodule.span (𝓞 K') (ι '' s)) : tw b ι c g.toLinearMap x ∈ Submodule.span (𝓞 K') (ι '' s) := by
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨v, hv, rfl⟩ := h; rw [tw_map hc]; exact Submodule.subset_span ⟨v, hv, rfl⟩
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul r x _ h1 =>
    have := Submodule.smul_mem _ (RingOfIntegers.mapRingHom (g : K' →+* K') r) h1
    rw [← algebraMap_smul K'] at this
    rw [← algebraMap_smul K', tw_smul]
    exact this

theorem eq_sum_coord (hc : ∀ a : Fin n → K', c (∑ k, a k • ι (b k)) = a) (s : Set V) {x : V'}
    (hx : x ∈ Submodule.span (𝓞 K') (ι '' s)) : x = ∑ k, c x k • ι (b k) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨v, hv, rfl⟩ := h
    exact (tw_map hc 1 v).symm
  | zero => simp
  | add x y _ _ h1 h2 =>
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h1, ← h2]
  | smul r x _ h1 =>
    rw [← algebraMap_smul K', map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← h1]

end Twist

section Norms

variable {K K' V V' : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [StarRing K']
  [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V'] {κ : Type} [Fintype κ] [DecidableEq κ]
  {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}

omit [IsTotallyComplex K] [NumberField K] in

theorem cnorm_cols (hG' : IsGram b' X' N') (φ : V →ₛₗ[algebraMap K K'] V')
    (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x) {j : ℕ} (e : Fin j → V) (w : InfinitePlace K')
    (x : Fin j → K) :
    Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => w.embedding (algebraMap K K' (x k))) =
      N (w.embedding.comp (algebraMap K K')) (∑ k, x k • e k) := by
  have h := ht w.embedding (∑ k, x k • e k)
  rw [← (hG' w).2, map_sum] at h
  simp only [map_smulₛₗ] at h
  rw [normAt_sum] at h
  exact h

theorem normAt_gal (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x) {j : ℕ}
    (e : Fin j → V) (g : K' ≃ₐ[K] K') (w : InfinitePlace K') (a : Fin j → K') :
    Formalism.HermitianLatticesTheory.normAt b' X' w (∑ k, g (a k) • φ (e k)) = Formalism.HermitianLatticesTheory.normAt b' X' (g⁻¹ • w) (∑ k, a k • φ (e k)) := by
  obtain ⟨ε, hε, h1, h2⟩ : ∃ ε : ℂ →+* ℂ, Continuous ε ∧ (∀ σ x, N (ε.comp σ) x = N σ x) ∧
      ∀ y, (g⁻¹ • w).embedding y = ε (w.embedding (g y)) := by
    have hw : g⁻¹ • w = InfinitePlace.mk (w.embedding.comp (g : K' →+* K')) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]; rfl
    rw [hw]
    rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (g : K' →+* K')) with h | h
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, fun y => by rw [h]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, hc, fun y => by rw [h]; rfl⟩
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have hd' : DenseRange (fun (x : Fin j → K) (k : Fin j) => σ (x k)) := DenseRange.piMap fun _ => hd
  have h3 : ∀ y : Fin j → ℂ, Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ y) =
      Formalism.HermitianLatticesTheory.cnorm (cols b' X' (g⁻¹ • w) (fun k => φ (e k)) *ᵥ fun k => ε (y k)) := fun y => by
    refine hd'.induction_on y (isClosed_eq ?_ ?_) fun x => ?_
    · unfold Formalism.HermitianLatticesTheory.cnorm Matrix.mulVec dotProduct; fun_prop
    · unfold Formalism.HermitianLatticesTheory.cnorm Matrix.mulVec dotProduct; fun_prop
    · have e1 : (g⁻¹ • w).embedding.comp (algebraMap K K') = ε.comp σ := RingHom.ext fun y => by
        simp [h2, hσ]
      have e2 := cnorm_cols hG' φ ht e (g⁻¹ • w) x
      rw [e1, h1] at e2
      refine (cnorm_cols hG' φ ht e w x).trans (e2.symm.trans ?_)
      simp [h2, hσ]
  rw [normAt_sum, normAt_sum, h3]
  simp only [h2]

theorem norm_realize_gal (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x) {j : ℕ}
    (e : Fin j → V) (g : K' ≃ₐ[K] K') (a : Fin j → K') :
    ‖Formalism.HermitianLatticesTheory.realize b' X' (∑ k, g (a k) • φ (e k))‖ = ‖Formalism.HermitianLatticesTheory.realize b' X' (∑ k, a k • φ (e k))‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_realize_sq, norm_realize_sq]
  simp only [normAt_gal hG' hc φ ht]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) fun w => Formalism.HermitianLatticesTheory.normAt b' X' w (∑ k, a k • φ (e k)) ^ 2

theorem gram_ge [StarRing K] {μ : Type} [Fintype μ] [DecidableEq μ] {b : Basis μ K V}
    {X : InfinitePlace K → Matrix μ μ ℂ} (hG : IsGram b X N) (hG' : IsGram b' X' N')
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤ (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) =
      1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) := fun x =>
    (cnorm_cols hG' φ ht e w x).symm.trans (one_mul _).symm
  rw [hv, gramPl_eq, gramPl_eq]
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine (det_le_of_dense σ hd _ _ 1 fun x => le_of_eq (Eq.trans ?_ (h1 x))).trans (by simp)
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine (det_le_of_dense σ hd _ _ 1 fun x => le_of_eq (Eq.trans ?_ (h1 x))).trans (by simp)
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine (this.trans ?_).symm
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]

end Norms

theorem slope_sq_span_le {K K' V V' : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K']
    [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V']
    [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] {N : (K →+* ℂ) → V → ℝ}
    {N' : (K' →+* ℂ) → V' → ℝ} (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (hg : HasGram N)
    (hg' : HasGram N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    (hL : L.FG) (h0 : L ≠ ⊥) (hN : ∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) :
    (Submodule.span (𝓞 K') (ι '' (L : Set V))).FG ∧
      slope_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slope_sq N L := by
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hg
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hg'
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K V := Module.Finite.of_basis b
  letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))
  haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let l : L →ₗ[𝓞 K] V' :=
    { toFun := fun x => ι x
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x
        rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
        rfl }
  have hr : Set.range l = ι '' (L : Set V) := by
    ext y; simp [l]
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'
  have hL'fg : L'.FG := by
    haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 K) (M := L)
    refine ⟨(s.finite_toSet.image l).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, ← Submodule.span_span_of_tower (𝓞 K), ← Submodule.map_span, hs,
      Submodule.map_top, LinearMap.coe_range, hr]
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L h0
  have hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V)) := rfl
  rw [hj] at hj0
  generalize finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj hj0
  have he' := hli j e he
  have hj' : Formalism.HN.rkK L' = j := by
    have : Submodule.span K' (L' : Set V') = Submodule.span K' (Set.range fun k => ι (e k)) := by
      rw [hL', Submodule.span_span_of_tower]
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.subset_span hx)
        rw [map_sum]
        exact Submodule.sum_mem _ fun k _ => by
          rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩
    rw [Formalism.HN.rkK, this, finrank_span_eq_card he', Fintype.card_fin]
  obtain ⟨i1, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' L' hL'fg
    (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)) hj'
  let eL : Fin j → L := fun k => ⟨e k, heL k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  rw [hidx] at i1 m1
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  have hidx' := relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr] at hidx'
  have m3 := m2
  rw [show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _
    from hidx', Nat.cast_pow, Real.log_pow] at m3
  have hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re :=
    Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)
  rw [sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re] at hs
  have hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K := by
    simpa [Formalism.HN.nPl] using sum_comap K K' fun _ => 1
  have hf' : (0 : ℝ) < Formalism.HN.nPl K' := lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm
  have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
  refine ⟨hL'fg, ?_⟩
  rw [slope_sq_eq hG hL, slope_sq_eq hG' hL'fg]
  refine le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp
  have m4 := congrArg ((finrank K K' : ℝ) * ·) m1
  rw [m3, hf]
  linarith

theorem slopeMax_sq_span_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [IsGalois K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L hg hg' hc hli hL h0 hN
  have hL' := (slope_sq_span_le ι L hg hg' hc hli hL h0 hN).1
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := id hg
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := id hg'
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  change IsGram b X N at hG
  change IsGram b' X' N' at hG'
  obtain ⟨c, hcc⟩ := exists_coord b ι (hli n b b.linearIndependent)
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'def
  have h0' : L' ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    refine (Submodule.ne_bot_iff _).2 ⟨ι v, Submodule.subset_span ⟨v, hv, rfl⟩, ?_⟩
    exact (hli 1 (fun _ => v) (linearIndependent_unique_iff.2 hv0)).ne_zero 0
  have hX' : ∀ v, IsUnit (X' v).det := fun v => (hG' v).1
  have hlat := (Formalism.HN.plLat K' V' _ b' X' hX' L' hL').1
  have hfg : ∀ M, M ≤ L' → M.FG := fun M hM => by
    haveI : IsNoetherian (𝓞 K') L' := isNoetherian_of_fg_of_noetherian L' hL'
    exact isNoetherian_submodule.1 inferInstance M hM
  obtain ⟨hsub, hmono, -, hrk, -⟩ := Formalism.HN.satBasic _ _ _ _ L' hlat
  obtain ⟨M, hM, hM0, hMd, hMt⟩ := exists_top_step _ hlat h0'
  let W : Submodule K' V' := Submodule.span K' (M : Set V')
  have hst : ∀ g : K' ≃ₐ[K] K', ∀ x ∈ M, tw b ι c g.toLinearMap x ∈ M := fun g x hx => by
    have h1 : twLat (b := b) (ι := ι) (c := c) g M ≤ L' := by
      rintro _ ⟨y, hy, rfl⟩
      exact tw_mem_span hcc g _ (hM hy)
    obtain ⟨e1, e2⟩ := rk_deg_image (Formalism.HermitianLatticesTheory.realize b' X') (tw b ι c g.toLinearMap) (hsub M hM) (hsub _ h1)
      (fun y => Iff.rfl) (fun y hy => by
        conv_rhs => rw [eq_sum_coord hcc _ (hM hy)]
        exact norm_realize_gal hG' hc ι hN b g (c y))
    exact hMt _ h1 (by rw [e1, e2, hMd]) ⟨x, hx, rfl⟩
  have hW : ∀ g : K' ≃ₐ[K] K', ∀ x ∈ W, tw b ι c g.toLinearMap x ∈ W := fun g x hx => by
    induction hx using Submodule.span_induction with
    | mem x h => exact Submodule.subset_span (hst g x h)
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul a x _ h1 => rw [tw_smul]; exact W.smul_mem _ h1
  have hMW : L' ⊓ W.restrictScalars (𝓞 K') = M := by
    have h1 : M ≤ L' ⊓ W.restrictScalars (𝓞 K') := fun x hx => ⟨hM hx, Submodule.subset_span hx⟩
    have h2 : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b' X') M =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b' X') (L' ⊓ W.restrictScalars (𝓞 K')) := by
      rw [(Formalism.HN.plLat K' V' _ b' X' hX' M (hfg M hM)).2.1,
        (Formalism.HN.plLat K' V' _ b' X' hX' _ (hfg _ inf_le_left)).2.1, Formalism.HN.rkK, Formalism.HN.rkK,
        le_antisymm (Submodule.span_mono (R := K') h1) (Submodule.span_le.2 fun x hx => hx.2)]
    refine le_antisymm (hMt _ inf_le_left ?_) h1
    rw [← h2, ← hMd]
    exact (hmono _ _ h1 inf_le_left).2 h2
  rw [hL'def, inf_eq_span hcc hW L] at hMW
  set M₀ : Submodule (𝓞 K) V := L ⊓ (W.comap ι).restrictScalars (𝓞 K) with hM₀
  have hM₀fg : M₀.FG := by
    haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
    exact isNoetherian_submodule.1 inferInstance M₀ inf_le_left
  have hM₀0 : M₀ ≠ ⊥ := fun h => hM0 (by rw [← hMW, h]; simp)
  have h1 := (slope_sq_span_le ι M₀ hg hg' hc hli hM₀fg hM₀0 hN).2
  rw [hMW, slope_sq_eq hG' (hfg M hM), slope_sq_eq hG hM₀fg] at h1
  rw [(slopeMax_slopeMin_eq hG' hL' h0').1, (slopeMax_slopeMin_eq hG hL h0).1]
  have h2 : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b' X') M = Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b' X') L' :=
    (div_eq_iff (Nat.cast_ne_zero.2 fun h => hM0 ((hrk M hM).1 h))).2 hMd
  have hlat₀ := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL).1
  have h3 : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) M₀ ≤ Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) L :=
    (div_le_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h =>
      hM₀0 (((Formalism.HN.satBasic _ _ _ _ L hlat₀).2.2.2.1 M₀ inf_le_left).1 h)))).2
      (((Formalism.HN.muChar _ _ _ _ L hlat₀ h0).1 _).1 le_rfl M₀ inf_le_left)
  unfold Formalism.HN.muDef at h1
  unfold Formalism.HN.muMaxDef
  linarith

end GlobalTheory.SlopeGal
