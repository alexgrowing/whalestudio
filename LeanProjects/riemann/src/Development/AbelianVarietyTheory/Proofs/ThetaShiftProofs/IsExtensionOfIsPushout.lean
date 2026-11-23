import Mathlib

noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

section Basic

variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

def IsCoord (a : V →ₛₗ[algebraMap K F] W) (ℓ : F →ₗ[K] K) (Λ : W →+ V) : Prop :=
  ∀ c v, Λ (c • a v) = ℓ c • v

structure IsExtension (a : V →ₛₗ[algebraMap K F] W) : Prop where
  span : Submodule.span F (Set.range a) = ⊤
  coord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ

private theorem semilinear_range_span_induction {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) (p : W → Prop) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hb : ∀ (c : F) v, p (c • a v)) (x : W) : p x := by
  have key : ∀ y ∈ Submodule.span F (Set.range a), ∀ c : F, p (c • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact fun c => hb c v
    | zero => intro c; rw [smul_zero]; exact h0
    | add y z _ _ hy hz => intro c; rw [smul_add]; exact hadd _ _ (hy c) (hz c)
    | smul d y _ hy => intro c; rw [smul_smul]; exact hy (c * d)
  have hx : x ∈ Submodule.span F (Set.range a) := by rw [h]; exact Submodule.mem_top
  simpa using key x hx 1

theorem addHom_ext {a : V →ₛₗ[algebraMap K F] W} (h : Submodule.span F (Set.range a) = ⊤)
    {M : Type} [AddCommGroup M] {f g : W →+ M} (e : ∀ (c : F) v, f (c • a v) = g (c • a v)) (x : W) :
    f x = g x := by
  exact semilinear_range_span_induction h (fun x => f x = g x) (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy]) e x

theorem IsCoord.natural {V' W' : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module F W']
    {a : V →ₛₗ[algebraMap K F] W} {a' : V' →ₛₗ[algebraMap K F] W'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : W →+ V} {Λ' : W' →+ V'}
    (hΛ : IsCoord a ℓ Λ) (hΛ' : IsCoord a' ℓ Λ') (θ : V →ₗ[K] V') (θ' : W →ₗ[F] W')
    (hθ : ∀ v, θ' (a v) = a' (θ v)) (x : W) : Λ' (θ' x) = θ (Λ x) := by
  have key := addHom_ext h (f := Λ'.comp θ'.toAddMonoidHom) (g := θ.toAddMonoidHom.comp Λ)
    (fun c v => by
      show Λ' (θ' (c • a v)) = θ (Λ (c • a v))
      rw [map_smul, hθ, hΛ' c (θ v), hΛ c v, map_smul]) x
  exact key

theorem exists_expansion {ι : Type} (b : Module.Basis ι K F) {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) {Λ : ι → W →+ V} (hΛ : ∀ i, IsCoord a (b.coord i) (Λ i))
    (x : W) : ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x) := by
  classical
  refine semilinear_range_span_induction h
    (fun x => ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x)) ?_ ?_ ?_ x
  · exact ⟨∅, fun i _ => map_zero _, fun S' _ => by simp⟩
  · rintro x y ⟨S₁, h₁, h₁'⟩ ⟨S₂, h₂, h₂'⟩
    refine ⟨S₁ ∪ S₂, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [Finset.mem_union, not_or] at hi
      rw [map_add, h₁ i hi.1, h₂ i hi.2, add_zero]
    · simp only [map_add, smul_add, Finset.sum_add_distrib]
      rw [← h₁' S' (Finset.union_subset_left hS'), ← h₂' S' (Finset.union_subset_right hS')]
  · intro c v
    refine ⟨(b.repr c).support, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [hΛ i c v, Module.Basis.coord_apply, Finsupp.notMem_support_iff.mp hi, zero_smul]
    · have hterm : ∀ i, b i • a (Λ i (c • a v)) = (b.repr c i • b i) • a v := by
        intro i
        rw [hΛ i c v, Module.Basis.coord_apply, LinearMap.map_smulₛₗ, smul_smul,
          Algebra.smul_def (b.repr c i) (b i), mul_comm (b i)]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr c]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hS' (fun i r => r • b i) (fun i _ => zero_smul _ _)]

theorem IsExtension.eq_of_coord {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) {x y : W}
    (e : ∀ ℓ Λ, IsCoord a ℓ Λ → Λ x = Λ y) : x = y := by
  classical
  let β := Module.Free.chooseBasis K F
  choose Λ hΛ using fun i => h.coord (β.coord i)
  obtain ⟨S₁, -, h₁⟩ := exists_expansion β h.span hΛ x
  obtain ⟨S₂, -, h₂⟩ := exists_expansion β h.span hΛ y
  rw [h₁ (S₁ ∪ S₂) Finset.subset_union_left, h₂ (S₁ ∪ S₂) Finset.subset_union_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [e _ _ (hΛ i)]

theorem IsExtension.exists_sum {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) (x : W) :
    ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i) := by
  refine semilinear_range_span_induction h.span
    (fun x => ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i)) ?_ ?_ ?_ x
  · exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  · rintro x y ⟨n, c, v, rfl⟩ ⟨m, c', v', rfl⟩
    refine ⟨n + m, Fin.append c c', Fin.append v v', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro c v
    exact ⟨1, fun _ => c, fun _ => v, by simp⟩

theorem IsExtension.of_proj {J : Type} {P Q : J → Type} [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module F (Q j)] (a : V →ₛₗ[algebraMap K F] W)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] Q j) (hb : ∀ j, IsExtension (b j))
    (π : ∀ j, V →ₗ[K] P j) (π' : ∀ j, W →ₗ[F] Q j) (comm : ∀ j v, π' j (a v) = b j (π j v))
    (inj' : ∀ x, (∀ j, π' j x = 0) → x = 0) (T : Finset J) (inj : ∀ v, (∀ j ∈ T, π j v = 0) → v = 0)
    (desc : ∀ (ℓ : F →ₗ[K] K) (Λ : ∀ j, Q j →+ P j), (∀ j, IsCoord (b j) ℓ (Λ j)) →
      ∀ x, ∃ v, ∀ j, π j v = Λ j (π' j x)) : IsExtension a := by
  classical
  have hcoord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ := by
    intro ℓ
    choose Λj hΛj using fun j => (hb j).coord ℓ
    choose f hf using desc ℓ Λj hΛj
    have uniq : ∀ v v' : V, (∀ j, π j v = π j v') → v = v' := fun v v' e =>
      sub_eq_zero.mp (inj _ (fun j _ => by rw [map_sub, e j, sub_self]))
    refine ⟨{ toFun := f
              map_zero' := uniq _ _ (fun j => by simp [hf])
              map_add' := fun x y => uniq _ _ (fun j => by simp [hf]) }, fun c v => ?_⟩
    refine uniq _ _ (fun j => ?_)
    show π j (f (c • a v)) = π j (ℓ c • v)
    rw [hf, map_smul, comm, hΛj j c (π j v), map_smul]
  refine ⟨?_, hcoord⟩
  let β := Module.Free.chooseBasis K F
  choose Λj hΛj using fun j i => (hb j).coord (β.coord i)
  rw [eq_top_iff]
  intro x _
  choose v hv using fun i => desc (β.coord i) (fun j => Λj j i) (fun j => hΛj j i) x
  choose S hS hS' using fun j => exists_expansion β (hb j).span (fun i => hΛj j i) (π' j x)
  have hv0 : ∀ i ∉ T.biUnion S, v i = 0 := fun i hi => inj _ (fun j hj => by
    rw [hv i j]
    exact hS j i (fun h => hi (Finset.mem_biUnion.mpr ⟨j, hj, h⟩)))
  have hx : x = ∑ i ∈ T.biUnion S, β i • a (v i) := by
    refine (sub_eq_zero.mp (inj' _ (fun j => ?_)))
    rw [map_sub, sub_eq_zero, map_sum]
    simp only [map_smul, comm, hv]
    conv_lhs => rw [hS' j (T.biUnion S ∪ S j) Finset.subset_union_right]
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    rw [← hv i j, hv0 i hi, map_zero, map_zero, smul_zero]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩))

theorem isExtension_of_isPushout {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra F B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [IsScalarTower K F B] [H : Algebra.IsPushout K F A B]
    (a : A →ₛₗ[algebraMap K F] B) (ha : ∀ x, a x = algebraMap A B x) : IsExtension a := by
  have hb : ∀ (c : F) (v : A), H.out.equiv (c ⊗ₜ v) = c • a v := by
    intro c v
    rw [IsBaseChange.equiv_tmul, ha]
    rfl
  refine ⟨?_, fun ℓ => ?_⟩
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := H.out.equiv.surjective y
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c v => rw [hb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
    | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
  · refine ⟨(TensorProduct.lid K A).toLinearMap.toAddMonoidHom.comp
      ((TensorProduct.map ℓ LinearMap.id).toAddMonoidHom.comp
        H.out.equiv.symm.toLinearMap.toAddMonoidHom), fun c v => ?_⟩
    show TensorProduct.lid K A (TensorProduct.map ℓ LinearMap.id (H.out.equiv.symm (c • a v))) = ℓ c • v
    rw [← hb, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      LinearMap.id_apply]

end Basic

section Graph

variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]

theorem graph_bijective (X : Submodule R (V₀ × ∀ j, P₀ j))
    (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : ∀ j, P₀ j →ₛₗ[algebraMap R K] P j)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] P' j) (hb : ∀ j, IsExtension (b j))
    (d : W →ₛₗ[algebraMap K F] W') (hd : IsExtension d)
    (π : ∀ j, W →ₗ[K] P j) (π' : ∀ j, W' →ₗ[F] P' j) (comm : ∀ j w, π' j (d w) = b j (π j w))
    (E : V → W → Prop)
    (hE : ∀ v w, E v w ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ X, ρ x.1 = algebraMap R K r • v ∧
      ∀ j, ρ' j (x.2 j) = algebraMap R K r • π j w)
    (bij : (∀ v, ∃! w, E v w) ∧ ∀ w, ∃! v, E v w)
    (E' : V' → W' → Prop)
    (hE' : ∀ v w, E' v w ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → V₀ × ∀ j, P₀ j), (∀ i, x i ∈ X) ∧
      v = ∑ i, c i • a (ρ (x i).1) ∧ ∀ j, π' j w = ∑ i, c i • b j (ρ' j ((x i).2 j))) :
    (∀ v, ∃! w, E' v w) ∧ ∀ w, ∃! v, E' v w := by
  classical
  have key : ∀ v w, E' v w → ∀ (ℓ : F →ₗ[K] K) (Λa : V' →+ V) (Λd : W' →+ W),
      IsCoord a ℓ Λa → IsCoord d ℓ Λd → E (Λa v) (Λd w) := by
    intro v w hvw ℓ Λa Λd hΛa hΛd
    obtain ⟨n, c, x, hx, rfl, hw⟩ := (hE' v w).mp hvw
    choose Λb hΛb using fun j => (hb j).coord ℓ
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun i => ℓ (c i))
    choose s hs using fun i => RingHom.mem_rangeS.mp (ht i)
    have hcoef : ∀ i, algebraMap R K (s i) = algebraMap R K (t : R) * ℓ (c i) := by
      intro i; rw [hs i, Algebra.smul_def]
    rw [hE]
    refine ⟨t, nonZeroDivisors.ne_zero t.2, ∑ i, s i • x i,
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hx i)), ?_, fun j => ?_⟩
    · rw [Prod.fst_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_fst, LinearMap.map_smulₛₗ, hΛa (c i) _, hcoef i, smul_smul]
    · have hnat := IsCoord.natural hd.span hΛd (hΛb j) (π j) (π' j) (comm j) w
      rw [← hnat, hw j, map_sum, Prod.snd_sum, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_snd, Pi.smul_apply, LinearMap.map_smulₛₗ, hΛb j (c i) _, hcoef i, smul_smul]
  have hne : ∀ r : R, r ≠ 0 → algebraMap K F (algebraMap R K r) ≠ 0 := fun r hr =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)
  have hcancel : ∀ (c : F) (r : R), r ≠ 0 →
      (c * (algebraMap K F (algebraMap R K r))⁻¹) * algebraMap K F (algebraMap R K r) = c :=
    fun c r hr => by rw [mul_assoc, inv_mul_cancel₀ (hne r hr), mul_one]
  refine ⟨fun v => ?_, fun w => ?_⟩
  · obtain ⟨n, c, u, rfl⟩ := ha.exists_sum v
    choose φ hφ using fun i => (bij.1 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (u i)) (∑ i, c i • d (φ i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun w' hw' => hd.eq_of_coord (fun ℓ Λd hΛd => ?_)⟩
    obtain ⟨Λa, hΛa⟩ := ha.coord ℓ
    exact (bij.1 _).unique (key _ _ hw' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)
  · obtain ⟨n, c, u, rfl⟩ := hd.exists_sum w
    choose φ hφ using fun i => (bij.2 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (φ i)) (∑ i, c i • d (u i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun v' hv' => ha.eq_of_coord (fun ℓ Λa hΛa => ?_)⟩
    obtain ⟨Λd, hΛd⟩ := hd.coord ℓ
    exact (bij.2 _).unique (key _ _ hv' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)

end Graph

end GlobalTheory.FieldBaseChange
