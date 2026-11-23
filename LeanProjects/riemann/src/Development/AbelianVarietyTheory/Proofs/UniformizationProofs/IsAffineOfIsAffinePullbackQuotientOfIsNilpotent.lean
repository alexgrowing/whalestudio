import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace GlobalTheory.AffineThickening

noncomputable def rs {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE h).op).hom

theorem rs_rs {Y : Scheme.{u}} {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(Y, U)) :
    rs h' (rs h a) = rs (h'.trans h) a := by
  simp only [rs, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem basicOpen_rs {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    Y.basicOpen (rs h a) = V ⊓ Y.basicOpen a :=
  Y.basicOpen_res a (homOfLE h).op

theorem exists_pow_mul_eq_zero {Y : Scheme.{u}} {U V : Y.Opens} (hU : IsAffineOpen U)
    (h : V ≤ U) (g a : Γ(Y, U)) (e : V = Y.basicOpen g) (ha : rs h a = 0) :
    ∃ n : ℕ, g ^ n * a = 0 := by
  subst e
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hU a g ha

theorem exists_eq_pow_mul {Y : Scheme.{u}} {U V : Y.Opens} (hU : IsAffineOpen U)
    (h : V ≤ U) (g : Γ(Y, U)) (x : Γ(Y, V)) (e : V = Y.basicOpen g) :
    ∃ (n : ℕ) (y : Γ(Y, U)), rs h y = rs h g ^ n * x := by
  subst e
  exact exists_eq_pow_mul_of_isAffineOpen Y U hU g x

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)

theorem app_rs {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (i.app V).hom (rs h a) = rs (i.preimage_mono h) ((i.app U).hom a) := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  exact this

def Lifts (U : Y.Opens) (a : Γ(Y, U)) (r : Γ(Z, ⊤)) : Prop :=
  (i.app U).hom a = rs le_top r

variable {i}

namespace Lifts

variable {U V : Y.Opens} {a b : Γ(Y, U)} {r s : Γ(Z, ⊤)}

theorem res (ha : Lifts i U a r) (h : V ≤ U) : Lifts i V (rs h a) r := by
  unfold Lifts at *
  rw [app_rs, ha, rs_rs]

theorem add (ha : Lifts i U a r) (hb : Lifts i U b s) : Lifts i U (a + b) (r + s) := by
  unfold Lifts at *
  rw [map_add, map_add, ha, hb]

theorem sub (ha : Lifts i U a r) (hb : Lifts i U b s) : Lifts i U (a - b) (r - s) := by
  unfold Lifts at *
  rw [map_sub, map_sub, ha, hb]

theorem mul (ha : Lifts i U a r) (hb : Lifts i U b s) : Lifts i U (a * b) (r * s) := by
  unfold Lifts at *
  rw [map_mul, map_mul, ha, hb]

theorem pow (ha : Lifts i U a r) (n : ℕ) : Lifts i U (a ^ n) (r ^ n) := by
  unfold Lifts at *
  rw [map_pow, map_pow, ha]

theorem zero : Lifts i U 0 0 := by
  unfold Lifts
  rw [map_zero, map_zero]

theorem one : Lifts i U 1 1 := by
  unfold Lifts
  rw [map_one, map_one]

theorem sub_zero (ha : Lifts i U a r) (hb : Lifts i U b r) : Lifts i U (a - b) 0 := by
  simpa using ha.sub hb

theorem mul_zero (a : Γ(Y, U)) (hb : Lifts i U b 0) : Lifts i U (a * b) 0 := by
  unfold Lifts at *
  rw [map_mul, hb, map_zero, MulZeroClass.mul_zero]

theorem zero_iff : Lifts i U a 0 ↔ (i.app U).hom a = 0 := by
  unfold Lifts
  rw [map_zero]

theorem preimage_basicOpen (ha : Lifts i U a r) :
    i ⁻¹ᵁ Y.basicOpen a = i ⁻¹ᵁ U ⊓ Z.basicOpen r := by
  rw [Scheme.preimage_basicOpen, ← basicOpen_rs le_top, ← ha]

end Lifts

theorem eq_of_preimage_eq [Surjective i] {U V : Y.Opens} (h : i ⁻¹ᵁ U = i ⁻¹ᵁ V) : U = V := by
  ext y
  obtain ⟨z, rfl⟩ := i.surjective y
  exact SetLike.ext_iff.1 h z

theorem exists_lifts [IsClosedImmersion i] {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Z, ⊤)) :
    ∃ a, Lifts i U a r :=
  i.app_surjective U hU _

theorem Lifts.basicOpen_eq [Surjective i] {U D : Y.Opens} {a : Γ(Y, U)} {r : Γ(Z, ⊤)}
    (ha : Lifts i U a r) (hD : i ⁻¹ᵁ D = Z.basicOpen r) : U ⊓ D = Y.basicOpen a := by
  apply eq_of_preimage_eq (i := i)
  rw [ha.preimage_basicOpen, Scheme.Hom.preimage_inf, hD]

theorem isAffineOpen_inf [IsClosedImmersion i] [Surjective i] {U D : Y.Opens}
    (hU : IsAffineOpen U) {r : Γ(Z, ⊤)} (hD : i ⁻¹ᵁ D = Z.basicOpen r) :
    IsAffineOpen (U ⊓ D) := by
  obtain ⟨a, ha⟩ := exists_lifts (i := i) hU r
  rw [ha.basicOpen_eq hD]
  exact hU.basicOpen a

theorem exists_forall_of_mono {α : Type*} [Finite α] (P : α → ℕ → Prop)
    (hP : ∀ a n, P a n → P a (n + 1)) (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by
  choose n hn using h
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  exact ⟨N, fun a ↦ Nat.le_induction (hn a) (fun m _ ↦ hP a m) N (hN ⟨a, rfl⟩)⟩

section Cover

variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)

variable (i σ) in

def IsCoboundary (r : Γ(Z, ⊤)) : Prop :=
  ∃ ρ t : ∀ j, Γ(Y, U j), (∀ j, Lifts i (U j) (ρ j) r) ∧ (∀ j, Lifts i (U j) (t j) 0) ∧
    ∀ j k, rs (inf_le_left : U j ⊓ U k ≤ U j) (t j) - rs inf_le_right (t k) =
      rs inf_le_left (ρ j) * (rs inf_le_left (σ j) - rs inf_le_right (σ k))

include hK hU hD in
theorem IsCoboundary.mul {r : Γ(Z, ⊤)} (r' : Γ(Z, ⊤)) (h : IsCoboundary i σ r) :
    IsCoboundary i σ (r' * r) := by
  obtain ⟨ρ, t, hρ, ht, e⟩ := h
  choose ρ' hρ' using fun j ↦ exists_lifts (i := i) (hU j) r'
  refine ⟨fun j ↦ ρ' j * ρ j, fun j ↦ ρ' j * t j, fun j ↦ (hρ' j).mul (hρ j),
    fun j ↦ Lifts.mul_zero _ (ht j), fun j k ↦ ?_⟩
  have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
    (((hρ' j).res inf_le_left).sub_zero ((hρ' k).res inf_le_right)) ((ht k).res inf_le_right)
  simp only [map_mul]
  linear_combination rs inf_le_left (ρ' j) * e j k + h0

omit [IsClosedImmersion i] [Surjective i] in
theorem IsCoboundary.add {r r' : Γ(Z, ⊤)} (h : IsCoboundary i σ r) (h' : IsCoboundary i σ r') :
    IsCoboundary i σ (r + r') := by
  obtain ⟨ρ, t, hρ, ht, e⟩ := h
  obtain ⟨ρ', t', hρ', ht', e'⟩ := h'
  refine ⟨fun j ↦ ρ j + ρ' j, fun j ↦ t j + t' j, fun j ↦ (hρ j).add (hρ' j),
    fun j ↦ by simpa using (ht j).add (ht' j), fun j k ↦ ?_⟩
  simp only [map_add]
  linear_combination e j k + e' j k

omit [IsClosedImmersion i] [Surjective i] in
theorem isCoboundary_zero : IsCoboundary i σ 0 :=
  ⟨0, 0, fun _ ↦ Lifts.zero, fun _ ↦ Lifts.zero, fun j k ↦ by simp⟩

include hK hU hD hσ in
theorem exists_isCoboundary_pow [Finite ι] (m : ι) : ∃ n : ℕ, IsCoboundary i σ (f m ^ n) := by
  choose g hg using fun j ↦ exists_lifts (i := i) (hU j) (f m)
  have hc : ∀ j k, Lifts i (U j ⊓ U k) (rs inf_le_left (σ j) - rs inf_le_right (σ k)) 0 :=
    fun j k ↦ ((hσ j).res _).sub_zero ((hσ k).res _)
  obtain ⟨N, hN⟩ := exists_forall_of_mono (fun j n ↦ ∃ y : Γ(Y, U j), Lifts i (U j) y 0 ∧
      rs (inf_le_left : U j ⊓ U m ≤ U j) y =
        rs inf_le_left (g j) ^ n * (rs inf_le_left (σ j) - rs inf_le_right (σ m)))
    (by
      rintro j n ⟨y, hy, e⟩
      exact ⟨g j * y, hy.mul_zero _, by rw [map_mul, e]; ring⟩)
    (by
      intro j
      obtain ⟨n, y, e⟩ := exists_eq_pow_mul (hU j) (inf_le_left : U j ⊓ U m ≤ U j) (g j)
        (rs inf_le_left (σ j) - rs inf_le_right (σ m)) ((hg j).basicOpen_eq (hD m))
      have h0 := (hc j m).mul_zero (rs inf_le_left (g j) ^ n)
      rw [← e, Lifts.zero_iff, app_rs] at h0
      obtain ⟨n', e'⟩ := exists_pow_mul_eq_zero ((hU j).preimage i) _ ((i.app (U j)).hom (g j)) _
        (by rw [(hg j).basicOpen_eq (hD m), Scheme.preimage_basicOpen]) h0
      refine ⟨n' + n, g j ^ n' * y, ?_, by rw [map_mul, map_pow, e]; ring⟩
      rw [Lifts.zero_iff, map_mul, map_pow, e'])
  choose t ht e using hN
  obtain ⟨M, hM⟩ := exists_forall_of_mono (fun (p : ι × ι) n ↦
      rs (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1) (g p.1) ^ n *
        (rs inf_le_left (t p.1) - rs inf_le_right (t p.2) - rs inf_le_left (g p.1) ^ N *
          (rs inf_le_left (σ p.1) - rs inf_le_right (σ p.2))) = 0)
    (by
      intro p n h
      rw [pow_succ', mul_assoc, h, mul_zero])
    (by
      rintro ⟨j, k⟩
      have hjk := isAffineOpen_inf (hU j) (hD k)
      refine exists_pow_mul_eq_zero hjk (inf_le_left : U j ⊓ U k ⊓ U m ≤ _) _ _
        (((hg j).res inf_le_left).basicOpen_eq (hD m)) ?_
      have hj : U j ⊓ U k ⊓ U m ≤ U j ⊓ U m := inf_le_inf_right _ inf_le_left
      have hk : U j ⊓ U k ⊓ U m ≤ U k ⊓ U m := inf_le_inf_right _ inf_le_right
      have ej := congrArg (rs hj) (e j)
      have ek := congrArg (rs hk) (e k)
      have h0 := hK _ (isAffineOpen_inf hjk (hD m)) _ _
        ((((hg j).res (hj.trans inf_le_left)).pow N).sub_zero
          (((hg k).res (hk.trans inf_le_left)).pow N)) ((hc k m).res hk)
      simp only [map_mul, map_sub, map_pow, rs_rs] at ej ek h0 ⊢
      linear_combination ej - ek + h0)
  refine ⟨M + N, fun j ↦ g j ^ (M + N), fun j ↦ g j ^ M * t j, fun j ↦ (hg j).pow _,
    fun j ↦ (ht j).mul_zero _, fun j k ↦ ?_⟩
  have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
    ((((hg j).res inf_le_left).pow M).sub_zero (((hg k).res inf_le_right).pow M))
    ((ht k).res inf_le_right)
  have h1 := hM (j, k)
  simp only [map_mul, map_pow] at h1 ⊢
  linear_combination h1 + h0

include hK hU hD hσ in
theorem isCoboundary_one [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) :
    IsCoboundary i σ 1 := by
  let P : Ideal Γ(Z, ⊤) :=
    { carrier := {r | IsCoboundary i σ r}
      add_mem' := IsCoboundary.add
      zero_mem' := isCoboundary_zero
      smul_mem' := fun c _ h ↦ IsCoboundary.mul hK hU hD c h }
  have : P.radical = ⊤ := by
    rw [eq_top_iff, ← hf, Ideal.span_le]
    rintro _ ⟨m, rfl⟩
    exact exists_isCoboundary_pow hK hU hD hσ m
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at this
  exact this

include hK hU hD in
theorem exists_lifts_top_of_cover [IsAffine Z] [Finite ι] (hf : Ideal.span (Set.range f) = ⊤)
    (s : Γ(Z, ⊤)) : ∃ a, Lifts i ⊤ a s := by
  choose σ hσ using fun j ↦ exists_lifts (i := i) (hU j) s
  obtain ⟨ρ, t, hρ, ht, e⟩ := isCoboundary_one hK hU hD hσ hf
  have hZ : ⊤ ≤ ⨆ j, i ⁻¹ᵁ U j := by
    have := ((isAffineOpen_top Z).iSup_basicOpen_eq_self_iff).2 hf
    rw [← this, iSup_le_iff]
    rintro ⟨_, j, rfl⟩
    exact le_iSup_of_le j (hD j).ge
  have hY : ⊤ ≤ ⨆ j, U j := by
    refine (eq_of_preimage_eq (i := i) ?_).le
    rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top]
    exact hZ.antisymm le_top
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hY
    (fun j ↦ σ j - t j) (fun j k ↦ by
      have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
        (Lifts.one.sub_zero ((hρ j).res inf_le_left))
        (((hσ j).res inf_le_left).sub_zero ((hσ k).res inf_le_right))
      change rs inf_le_left (σ j - t j) = rs inf_le_right (σ k - t k)
      simp only [map_sub]
      linear_combination h0 - e j k)
  refine ⟨a, Z.sheaf.eq_of_locally_eq' (fun j ↦ i ⁻¹ᵁ U j) (i ⁻¹ᵁ ⊤)
    (fun j ↦ homOfLE (i.preimage_mono le_top)) (le_top.trans hZ) _ _ fun j ↦ ?_⟩
  have h1 : rs le_top a = σ j - t j := ha j
  have h2 : (i.app (U j)).hom (σ j - t j) = rs le_top (s - 0) := (hσ j).sub (ht j)
  rw [← h1, sub_zero] at h2
  exact ((app_rs i le_top a).symm.trans h2).trans (rs_rs le_top _ s).symm

end Cover

theorem isAffine_of_mul_eq_zero (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i] [IsAffine Z]
    (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U),
      (i.app U).hom a = 0 → (i.app U).hom b = 0 → a * b = 0) : IsAffine Y := by
  have hK' : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U),
      Lifts i U a 0 → Lifts i U b 0 → a * b = 0 :=
    fun U hU a b ha hb ↦ hK U hU a b (Lifts.zero_iff.1 ha) (Lifts.zero_iff.1 hb)
  have hD : ∀ r : Γ(Z, ⊤), ∃ D : Y.Opens, i ⁻¹ᵁ D = Z.basicOpen r := fun r ↦ by
    obtain ⟨O, hO, hO'⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp (Z.basicOpen r).isOpen
    exact ⟨⟨O, hO⟩, Opens.ext hO'⟩
  choose D hD using hD
  have hS : Ideal.span {r | IsAffineOpen (D r)} = ⊤ := by
    rw [← (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro z _
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i z)) isOpen_univ
    obtain ⟨r, hr, hz⟩ := (isAffineOpen_top Z).exists_basicOpen_le (V := i ⁻¹ᵁ W) ⟨z, hzW⟩ trivial
    have e : W ⊓ D r = D r := eq_of_preimage_eq (i := i) (by
      rw [Scheme.Hom.preimage_inf, hD, inf_eq_right.2 hr])
    exact Opens.mem_iSup.2 ⟨⟨r, show IsAffineOpen (D r) from e ▸ isAffineOpen_inf hW (hD r)⟩, hz⟩
  obtain ⟨T, hT, hT'⟩ := (Ideal.span_eq_top_iff_finite _).1 hS
  have hsurj : ∀ s, ∃ a, Lifts i ⊤ a s :=
    exists_lifts_top_of_cover (ι := T) (f := fun r ↦ r.1) (U := fun r ↦ D r.1) hK'
      (fun r ↦ hT r.2) (fun r ↦ hD _) (by simpa using hT')
  choose g hg using hsurj
  refine isAffine_of_isAffineOpen_basicOpen (g '' T) ?_ ?_
  · have key : ∀ r ∈ Ideal.span (T : Set Γ(Z, ⊤)), ∃ a ∈ Ideal.span (g '' T), Lifts i ⊤ a r := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem x h => exact ⟨g x, Ideal.subset_span ⟨x, h, rfl⟩, hg x⟩
      | zero => exact ⟨0, zero_mem _, Lifts.zero⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha'⟩ := hx
        obtain ⟨b, hb, hb'⟩ := hy
        exact ⟨a + b, add_mem ha hb, ha'.add hb'⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha'⟩ := hx
        exact ⟨g c * a, Ideal.mul_mem_left _ _ ha, (hg c).mul ha'⟩
    obtain ⟨a, ha, ha'⟩ := key 1 (hT' ▸ Submodule.mem_top)
    refine Ideal.eq_top_of_isUnit_mem _ ha ?_
    have e : Y.basicOpen a = ⊤ := by
      rw [← ha'.basicOpen_eq (D := ⊤) (by simp), top_inf_eq]
    refine Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ a fun x hx ↦ ?_
    exact (Y.mem_basicOpen a x hx).1 (e.ge hx)
  · rintro _ ⟨r, hr, rfl⟩
    rw [← (hg r).basicOpen_eq (hD r), top_inf_eq]
    exact hT hr

theorem exists_ker_app_eq_map {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    ∃ α : A →+* Γ(Y, U), RingHom.ker (i.app U).hom = (RingHom.ker β.hom).map α := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact ⟨_, PrimeSection.ker_eq_map_of_isPushout hpo' hβ⟩

theorem isAffine_of_isPullback_of_sq_eq_bot {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) (hsq : RingHom.ker β.hom ^ 2 = ⊥) {f : Y ⟶ Spec A} {i : Z ⟶ Y}
    {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Z] : IsAffine Y := by
  have h1 := IsClosedImmersion.spec_of_surjective β hβ
  have h2 : Surjective (Spec.map β) := ⟨fun x ↦ by
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker β.hom : Set A) := fun a ha ↦
      x.isPrime.mem_of_pow_mem 2 (by
        have := Ideal.pow_mem_pow ha 2
        rw [hsq, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ β.hom hβ] at hx
    exact hx⟩
  have : IsClosedImmersion i := MorphismProperty.of_isPullback h.flip h1
  have : Surjective i := MorphismProperty.of_isPullback h.flip h2
  refine isAffine_of_mul_eq_zero i fun U hU a b ha hb ↦ ?_
  obtain ⟨α, hα⟩ := exists_ker_app_eq_map hβ h hU
  have h0 : RingHom.ker (i.app U).hom ^ 2 = ⊥ := by
    rw [hα, ← Ideal.map_pow, hsq, Ideal.map_bot]
  rw [← Ideal.mem_bot, ← h0, pow_two]
  exact Ideal.mul_mem_mul ha hb

theorem isAffine_of_isPullback_of_isNilpotent {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) : ∀ {C : CommRingCat.{u}} (β : CommRingCat.of A ⟶ C),
      Function.Surjective β → RingHom.ker β.hom = J → ∀ {Y Z : Scheme.{u}}
      {f : Y ⟶ Spec (.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}, IsPullback i f' f (Spec.map β) →
      IsAffine Z → IsAffine Y := by
  apply Ideal.IsNilpotent.induction_on (S := A) J hJ
  · intro S _ I hI C β hβ e Y Z f i f' h hZ
    exact isAffine_of_isPullback_of_sq_eq_bot hβ (e ▸ hI) h
  · intro S _ I I' hle h₁ h₂ C β hβ e Y Z f i f' h hZ
    let π : CommRingCat.of S ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    have hI : ∀ a ∈ I, β.hom a = 0 := fun a ha ↦ by
      rw [← RingHom.mem_ker, e]; exact hle ha
    let γ : CommRingCat.of (S ⧸ I) ⟶ C := CommRingCat.ofHom (Ideal.Quotient.lift I β.hom hI)
    have hγ : π ≫ γ = β := by ext; rfl
    have hs : Spec.map β = Spec.map γ ≫ Spec.map π := by rw [← Spec.map_comp, hγ]
    refine h₁ π Ideal.Quotient.mk_surjective Ideal.mk_ker (IsPullback.of_hasPullback f _) ?_
    refine h₂ γ (Ideal.Quotient.lift_surjective_of_surjective I hI hβ)
      (by rw [← e]; exact Ideal.ker_quotient_lift β.hom _)
      (f := pullback.snd f (Spec.map π)) (f' := f')
      (i := pullback.lift i (f' ≫ Spec.map γ) (by rw [h.w, hs, Category.assoc])) ?_ hZ
    exact IsPullback.of_right (by rwa [pullback.lift_fst, ← hs]) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f (Spec.map π))

end GlobalTheory.AffineThickening

namespace GlobalTheory

theorem isAffine_of_isAffine_pullback_quotient_of_isNilpotent (A : Type) [CommRing A]
    (J : Ideal A) (hJ : IsNilpotent J) (Y : Over (Spec (CommRingCat.of A)))
    (h : IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) :
    IsAffine Y.left :=
  AffineThickening.isAffine_of_isPullback_of_isNilpotent J hJ _ Ideal.Quotient.mk_surjective
    Ideal.mk_ker (IsPullback.of_hasPullback _ _) h

end GlobalTheory
