import Development.WeilBound.ThetaLifts.TowerModels.PlaneForm

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {v : Pl F} (τ : E →ₐ[F] Fv F v)

theorem map_mem_splitLat {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, AddSubgroup.subset_closure ⟨1, one_mem _, z, hz, rfl⟩,
    funext fun i => by simp [splitVec, splitProj_tmul]⟩

theorem splitLat_le {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v)) (hN : ∀ z ∈ L, (fun i => τ (z i)) ∈ N) :
    splitLat τ L ≤ N := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · have := N.smul_mem ⟨a, ha⟩ (hN x hx)
    convert this using 1
    funext i
    simp only [splitVec, splitProj_tmul]
    rfl
  · have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    rw [this]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have : splitVec τ (-y) = -splitVec τ y := funext fun _ => map_neg _ _
    rw [this]; exact neg_mem hy

theorem map_mem_of_unit {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {c : E} (hc : c • x ∈ L)
    (hv : Valued.v (τ c) = 1) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    (a • fun i => τ (x i)) ∈ splitLat τ L := by
  have h0 : τ c ≠ 0 := fun e => by simp [e] at hv
  have h1 : a * (τ c)⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem ha (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one])
  have := (splitLat τ L).smul_mem ⟨_, h1⟩ (map_mem_splitLat τ hc)
  convert this using 1
  funext i
  change a * τ (x i) = a * (τ c)⁻¹ * τ (c * x i)
  rw [map_mul]
  field_simp

theorem exists_basis (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ) (hn : n = n₁ + 2) (h01 : i₀ < i₁) (h1n : i₁ < n) (hlat : L.IsLattice E)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y)
    (hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1)
    (hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1)
    (hβ₁ : IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁) :
    ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  classical
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := j.2
    unfold skip; split_ifs <;> omega
  let f : Fin n₁ ⊕ Bool → Fin n := Sum.elim (fun j => ⟨skip i₀ i₁ j, hsk j⟩)
    fun b => cond b ⟨i₁, h1n⟩ ⟨i₀, h01.trans h1n⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hn]⟩
    rintro (a | _ | _) (b | _ | _) e <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, cond, Fin.mk.injEq, skip, Sum.inl.injEq, Fin.ext_iff] at e ⊢ <;>
      first | omega | (split_ifs at e <;> omega)
  let e := Equiv.ofBijective f hf
  let c : Fin n₁ ⊕ Bool → Fin n → Fv F v := Sum.elim (fun j r => (ι.map τ * β₁.1) r j)
    fun b => cond b (fun r => τ (y r)) fun r => τ (x r)
  let b : Matrix (Fin n) (Fin n) (Fv F v) := Matrix.of fun r i => c (e.symm i) r
  have hb : ∀ u : Fin n → Fv F v, b *ᵥ u = (u (e (.inr false)) • fun r => τ (x r)) +
      ι.map τ *ᵥ β₁.1 *ᵥ (fun j => u (e (.inl j))) + u (e (.inr true)) • fun r => τ (y r) := fun u => by
    funext r
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, b, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_bool, c, Sum.elim_inl, Sum.elim_inr, cond]
    ring
  have hmv : ∀ u : Fin n₁ → E, (fun i => τ ((ι *ᵥ u) i)) = ι.map τ *ᵥ fun j => τ (u j) := fun u =>
    funext fun i => RingHom.map_mulVec (τ : E →+* Fv F v) ι u i
  have hsurj : ∀ w ∈ splitLat τ L, ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w := by
    let N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) :=
      { carrier := {w | ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w}
        zero_mem' := ⟨0, fun _ => zero_mem _, Matrix.mulVec_zero _⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u + u', fun i => add_mem (hu i) (hu' i), Matrix.mulVec_add _ _ _⟩
        smul_mem' := by
          rintro a _ ⟨u, hu, rfl⟩
          exact ⟨(a : Fv F v) • u, fun i => mul_mem a.2 (hu i), Matrix.mulVec_smul _ _ _⟩ }
    refine fun w hw => splitLat_le τ N (fun z hz => ?_) hw
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hsplit z hz
    have hu' := hβ₁.mem_iff.1 (map_mem_splitLat τ (L := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) hu)
    refine ⟨fun i => Sum.elim ((β₁⁻¹).1 *ᵥ fun j => τ (u j)) (fun b => cond b (τ t) (τ s)) (e.symm i), fun i => ?_, ?_⟩
    · beta_reduce
      rcases e.symm i with j | _ | _
      · exact hu' j
      · exact hx.1 s hs
      · exact hy.1 t ht
    · rw [hb]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond]
      rw [Matrix.mulVec_mulVec _ β₁.1, Units.mul_inv, Matrix.one_mulVec, ← hmv]
      funext r
      simp
  have hunit : IsUnit b := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have h1 : ∀ z : Fin n → E, (fun i => τ (z i)) ∈ LinearMap.range b.mulVecLin := fun z => by
      have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hlat.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨u, -, hu⟩ := hsurj _ (map_mem_splitLat τ hz); exact ⟨u, hu⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, map_add]; exact add_mem ha ha'
      | smul a z _ hz => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ (τ a) hz
    intro w
    have : w = ∑ i, w i • fun k => τ ((Pi.single i 1 : Fin n → E) k) := by
      funext k
      simp [Pi.single_apply, apply_ite]
    rw [this]
    exact (Submodule.sum_mem (LinearMap.range b.mulVecLin) fun i _ => Submodule.smul_mem _ _ (h1 _))
  obtain ⟨β, hβ⟩ := hunit
  have col : ∀ k r, β.1 r (e k) = c k r := fun k r => by rw [hβ]; simp [b]
  refine ⟨β, fun i => ⟨fun hi r => ?_, fun hi r => ?_, fun j hi r => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · rw [show i = e (.inr false) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inr true) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inl j) from Fin.ext hi, col]; rfl
  · rw [hβ, hb]
    obtain ⟨s, hs, hs'⟩ := hx.2
    obtain ⟨t, ht, ht'⟩ := hy.2
    refine add_mem (add_mem (map_mem_of_unit τ hs hs' (hu _)) ?_) (map_mem_of_unit τ ht ht' (hu _))
    refine splitLat_le τ ((splitLat τ L).comap ((ι.map τ).mulVecLin.restrictScalars (v.adicCompletionIntegers F)))
      (fun z hz => ?_) ((hβ₁ _).1 fun j => hu _)
    change ι.map τ *ᵥ (fun j => τ (z j)) ∈ splitLat τ L
    rw [← hmv]
    exact map_mem_splitLat τ hz
  · obtain ⟨u', hu', e'⟩ := hsurj _ hu
    rw [← hβ] at e'
    rw [← Matrix.mulVec_injective_iff_isUnit.2 β.isUnit e']
    exact hu'

end PositivityTheory.ThKG.Tow.Pln

end
