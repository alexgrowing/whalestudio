import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open GlobalTheory.ThK.SplitInv

namespace GlobalTheory.ThK.SplitInv

theorem mem_fixIn_iff {H : Type} [Group H] (S : Submodule ℂ (H → ℂ)) (K : Subgroup H) (φ : H → ℂ) :
    φ ∈ fixIn S K ↔ φ ∈ S ∧ ∀ k ∈ K, rt k φ = φ := Iff.rfl

theorem rt_sub {H : Type} [Group H] (k : H) (φ ψ : H → ℂ) : rt k (φ - ψ) = rt k φ - rt k ψ := rfl

theorem rt_sum {H : Type} [Group H] (k : H) {ι : Type} (s : Finset ι) (f : ι → H → ℂ) :
    rt k (∑ i ∈ s, f i) = ∑ i ∈ s, rt k (f i) :=
  map_sum (LinearMap.funLeft ℂ ℂ (fun g : H => g * k)) f s

theorem compRed_of_unitary (H : Type) [Group H] (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) (𝒦 : Set (Subgroup H)) :
    RStable G₀ S → SmAdm G₀ S 𝒦 → Unitary G₀ S → CompRed G₀ S := by
  rintro hS ⟨hKG, hKK, hfix, hfd⟩ ⟨b, hlin, hher, hpos, hinv⟩ C hCS hC

  have b0l : ∀ χ ∈ S, b 0 χ = 0 := fun χ hχ => by
    have h := hlin 0 S.zero_mem 0 S.zero_mem χ hχ 1
    simp only [smul_zero, add_zero, one_mul] at h
    linear_combination -h
  have bal : ∀ φ ∈ S, ∀ ψ ∈ S, ∀ χ ∈ S, b (φ + ψ) χ = b φ χ + b ψ χ := fun φ hφ ψ hψ χ hχ => by
    simpa using hlin φ hφ ψ hψ χ hχ 1
  have bsl : ∀ φ ∈ S, ∀ χ ∈ S, ∀ c : ℂ, b (c • φ) χ = c * b φ χ := fun φ hφ χ hχ c => by
    simpa [b0l χ hχ] using hlin φ hφ 0 S.zero_mem χ hχ c
  have bsubl : ∀ φ ∈ S, ∀ ψ ∈ S, ∀ χ ∈ S, b (φ - ψ) χ = b φ χ - b ψ χ := fun φ hφ ψ hψ χ hχ => by
    have h := hlin ψ hψ φ hφ χ hχ (-1)
    rw [neg_one_smul, neg_add_eq_sub] at h
    rw [h]; ring
  have b0r : ∀ χ ∈ S, b χ 0 = 0 := fun χ hχ => by
    rw [hher χ hχ 0 S.zero_mem, b0l χ hχ, map_zero]
  have bar : ∀ χ ∈ S, ∀ φ ∈ S, ∀ ψ ∈ S, b χ (φ + ψ) = b χ φ + b χ ψ := fun χ hχ φ hφ ψ hψ => by
    rw [hher χ hχ _ (S.add_mem hφ hψ), bal φ hφ ψ hψ χ hχ, map_add, ← hher χ hχ φ hφ, ← hher χ hχ ψ hψ]
  have bsr : ∀ χ ∈ S, ∀ φ ∈ S, ∀ c : ℂ, b χ (c • φ) = starRingEnd ℂ c * b χ φ := fun χ hχ φ hφ c => by
    rw [hher χ hχ _ (S.smul_mem c hφ), bsl φ hφ χ hχ c, map_mul, ← hher χ hχ φ hφ]
  have bsumr : ∀ χ ∈ S, ∀ {ι : Type} (s : Finset ι) (f : ι → H → ℂ), (∀ x ∈ s, f x ∈ S) →
      b χ (∑ x ∈ s, f x) = ∑ x ∈ s, b χ (f x) := by
    intro χ hχ ι s f
    classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [b0r χ hχ]
    | @insert a s ha ih =>
      intro hs
      have hs' : ∀ x ∈ s, f x ∈ S := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert ha, Finset.sum_insert ha, bar χ hχ _ (hs a (Finset.mem_insert_self a s)) _ (S.sum_mem hs'),
        ih hs']

  let C' : Submodule ℂ (H → ℂ) :=
    { carrier := {φ | φ ∈ S ∧ ∀ c ∈ C, b φ c = 0}
      add_mem' := fun {φ ψ} hφ hψ => ⟨S.add_mem hφ.1 hψ.1, fun c hc => by
        rw [bal φ hφ.1 ψ hψ.1 c (hCS hc), hφ.2 c hc, hψ.2 c hc, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, fun c hc => b0l c (hCS hc)⟩
      smul_mem' := fun a φ hφ => ⟨S.smul_mem a hφ.1, fun c hc => by
        rw [bsl φ hφ.1 c (hCS hc), hφ.2 c hc, mul_zero]⟩ }
  have memC' : ∀ φ, φ ∈ C' ↔ φ ∈ S ∧ ∀ c ∈ C, b φ c = 0 := fun _ => Iff.rfl
  refine ⟨C', fun φ hφ => ((memC' φ).1 hφ).1, ?_, ?_, ?_⟩
  ·
    intro φ hφ k hk
    rw [memC'] at hφ ⊢
    refine ⟨hS φ hφ.1 k hk, fun c hc => ?_⟩
    have hc' : rt k⁻¹ c ∈ C := hC c hc k⁻¹ (G₀.inv_mem hk)
    have e : c = rt k (rt k⁻¹ c) := by rw [rt_rt, mul_inv_cancel, rt_one]
    rw [e, hinv φ hφ.1 _ (hCS hc') k hk, hφ.2 _ hc']
  ·
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_inf] at hc
    rw [Submodule.mem_bot]
    by_contra hne
    have h := hpos c (hCS hc.1) hne
    rw [((memC' c).1 hc.2).2 c hc.1] at h
    simp at h
  ·
    refine le_antisymm (sup_le hCS fun φ hφ => ((memC' φ).1 hφ).1) ?_
    intro φ hφS
    obtain ⟨K, hK, hφK⟩ := hfix φ hφS

    set V : Submodule ℂ (H → ℂ) := C ⊓ fixIn S K with hVdef
    have hVS : ∀ x ∈ V, x ∈ S := fun x hx => hCS (Submodule.mem_inf.1 hx).1
    haveI : FiniteDimensional ℂ (fixIn S K) := hfd K hK
    haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_right
    let e := Module.finBasis ℂ V

    have ext : ∀ x ∈ S, (∀ i, b x (e i) = 0) → ∀ w ∈ V, b x w = 0 := by
      intro x hx hxe w hw
      have hsum := congrArg Subtype.val (e.sum_repr ⟨w, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      rw [← hsum, bsumr x hx _ _ fun i _ => S.smul_mem _ (hVS _ (e i).2)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [bsr x hx _ (hVS _ (e i).2), hxe i, mul_zero]

    let T : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
      { toFun := fun v i => b v (e i)
        map_add' := fun v w => by
          funext i
          exact bal v (hVS _ v.2) w (hVS _ w.2) (e i) (hVS _ (e i).2)
        map_smul' := fun a v => by
          funext i
          exact bsl v (hVS _ v.2) (e i) (hVS _ (e i).2) a }
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker] at hv
      rw [Submodule.mem_bot]
      have h0 : ∀ w ∈ V, b v w = 0 := ext v (hVS _ v.2) fun i => congrFun hv i
      by_contra hne
      have hne' : (v : H → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
      have h := hpos v (hVS _ v.2) hne'
      rw [h0 v v.2] at h
      simp at h
    have hTsurj : Function.Surjective T :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Module.finrank_fin_fun ℂ).symm).1 hTinj
    obtain ⟨v, hv⟩ := hTsurj fun i => b φ (e i)
    have hvS : (v : H → ℂ) ∈ S := hVS _ v.2
    have hvC : (v : H → ℂ) ∈ C := (Submodule.mem_inf.1 v.2).1
    have hvK : ∀ k ∈ K, rt k (v : H → ℂ) = v := ((mem_fixIn_iff S K _).1 (Submodule.mem_inf.1 v.2).2).2

    have hψS : φ - v ∈ S := S.sub_mem hφS hvS
    have hψK : ∀ k ∈ K, rt k (φ - v) = φ - v := fun k hk => by rw [rt_sub, hφK k hk, hvK k hk]
    have hψV : ∀ w ∈ V, b (φ - v) w = 0 := by
      refine ext _ hψS fun i => ?_
      rw [bsubl φ hφS _ hvS _ (hVS _ (e i).2), sub_eq_zero]
      exact (congrFun hv i).symm

    have hψC : ∀ n ∈ C, b (φ - v) n = 0 := by
      intro n hn
      obtain ⟨K', hK', hnK'⟩ := hfix n (hCS hn)
      haveI : ((K ⊓ K').subgroupOf K).FiniteIndex := (hKK K hK K' hK').2
      haveI : Finite (K ⧸ ((K ⊓ K').subgroupOf K)) := Subgroup.finite_quotient_of_finiteIndex
      have hfinT : (Set.range fun g : K => rt (g : H) n).Finite := by
        refine (Set.finite_range fun q : K ⧸ ((K ⊓ K').subgroupOf K) =>
          Quotient.liftOn' q (fun g : K => rt (g : H) n) fun a c hac => ?_).subset ?_
        · have h1 : ((a⁻¹ * c : K) : H) ∈ K' :=
            (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hac))).2
          have h2 : (c : H) = a * ((a⁻¹ * c : K) : H) := by simp
          rw [h2, ← rt_rt, hnK' _ h1]
        · rintro _ ⟨g, rfl⟩
          exact ⟨QuotientGroup.mk g, rfl⟩
      set Tf := hfinT.toFinset with hTf
      have memT : ∀ x, x ∈ Tf ↔ ∃ g : K, rt (g : H) n = x := fun x => by
        rw [hTf, Set.Finite.mem_toFinset, Set.mem_range]
      have hTS : ∀ x ∈ Tf, x ∈ S := fun x hx => by
        obtain ⟨g, rfl⟩ := (memT x).1 hx
        exact hCS (hC n hn g (hKG K hK g.2))
      have hTC : ∀ x ∈ Tf, x ∈ C := fun x hx => by
        obtain ⟨g, rfl⟩ := (memT x).1 hx
        exact hC n hn g (hKG K hK g.2)

      have havg : (∑ x ∈ Tf, x) ∈ V := by
        refine Submodule.mem_inf.2 ⟨C.sum_mem hTC, (mem_fixIn_iff S K _).2 ⟨S.sum_mem hTS, fun k hk => ?_⟩⟩
        rw [rt_sum]
        refine Finset.sum_nbij' (rt k) (rt k⁻¹) ?_ ?_ ?_ ?_ fun _ _ => rfl
        · intro x hx
          obtain ⟨g, rfl⟩ := (memT x).1 hx
          exact (memT _).2 ⟨⟨k, hk⟩ * g, by rw [rt_rt]; rfl⟩
        · intro x hx
          obtain ⟨g, rfl⟩ := (memT x).1 hx
          exact (memT _).2 ⟨⟨k⁻¹, K.inv_mem hk⟩ * g, by rw [rt_rt]; rfl⟩
        · intro x _
          rw [rt_rt, inv_mul_cancel, rt_one]
        · intro x _
          rw [rt_rt, mul_inv_cancel, rt_one]
      have hall : ∀ x ∈ Tf, b (φ - v) x = b (φ - v) n := fun x hx => by
        obtain ⟨g, rfl⟩ := (memT x).1 hx
        have hg : (g : H) ∈ G₀ := hKG K hK g.2
        rw [← hinv _ hψS n (hCS hn) g hg, hψK g g.2]
      have hsum0 := hψV _ havg
      rw [bsumr _ hψS Tf (fun x => x) hTS, Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul] at hsum0
      have hcard : (Tf.card : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
        exact ⟨n, (memT n).2 ⟨1, rt_one n⟩⟩
      exact (mul_eq_zero.1 hsum0).resolve_left hcard
    have hψ : φ - v ∈ C' := (memC' _).2 ⟨hψS, hψC⟩
    have hφ : φ = (v : H → ℂ) + (φ - v) := by abel
    rw [hφ]
    exact Submodule.add_mem_sup hvC hψ

end GlobalTheory.ThK.SplitInv
