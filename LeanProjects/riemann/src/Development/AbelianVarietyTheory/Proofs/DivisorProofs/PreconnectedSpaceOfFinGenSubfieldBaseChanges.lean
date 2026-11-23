import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem flat_spec_field {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Sp K) : Flat f := by
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : A →+* B) (j : B →+* C) :
    spMap (j.comp i) = spMap j ≫ spMap i := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem appTop_spMap_injective {A B : Type} [CommRing A] [CommRing B] (j : A →+* B)
    (hj : Function.Injective j) : Function.Injective (spMap j).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap j).appTop.hom x) =
      j ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) := fun x => congrArg (fun f => f.hom x) e
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  rw [h3, h3] at h2
  have h4 := hj h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom h4
  simpa using this

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (j : A →+* B) (y : A) :
    (spMap j).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (j y) := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j)
  exact (congrArg (fun f => f.hom y) e).symm

variable {F : Type} [CommRing F] {X : Scheme.{0}} (f : X ⟶ Sp F)

def bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    pullback f (spMap i₀) ⟶ pullback f (spMap i) :=
  pullback.map f (spMap i₀) f (spMap i) (𝟙 X) (spMap j) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← hji, spMap_comp])

theorem bc_fst {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.fst f (spMap i) = pullback.fst f (spMap i₀) := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

theorem bc_snd {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.snd f (spMap i) = pullback.snd f (spMap i₀) ≫ spMap j := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    IsPullback (bc f i₀ i j hji) (pullback.snd f (spMap i₀)) (pullback.snd f (spMap i)) (spMap j) := by
  have s : IsPullback (bc f i₀ i j hji ≫ pullback.fst f (spMap i)) (pullback.snd f (spMap i₀)) f
      (spMap j ≫ spMap i) := by
    rw [bc_fst, ← spMap_comp, hji]
    exact IsPullback.of_hasPullback f (spMap i₀)
  exact IsPullback.of_right s (bc_snd f i₀ i j hji) (IsPullback.of_hasPullback f (spMap i))

theorem bc_trans {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i₀ : F →+* K) (i₁ : F →+* A) (j₁ : A →+* K) (h₁ : j₁.comp i₁ = i₀)
    (i₂ : F →+* B) (j₂ : B →+* K) (h₂ : j₂.comp i₂ = i₀) (k : A →+* B) (hk : k.comp i₁ = i₂)
    (hk' : j₂.comp k = j₁) :
    bc f i₀ i₁ j₁ h₁ = bc f i₀ i₂ j₂ h₂ ≫ bc f i₂ i₁ k hk := by
  apply pullback.hom_ext
  · simp [bc_fst]
  · rw [Category.assoc, bc_snd, bc_snd, ← Category.assoc, bc_snd, Category.assoc, ← spMap_comp, hk']

theorem mem_of_isPushout {R A B P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ B} {inl : A ⟶ P} {inr : B ⟶ P}
    (H : IsPushout φ ψ inl inr) (S : Subring P) (hA : ∀ a, inl.hom a ∈ S) (hB : ∀ b, inr.hom b ∈ S)
    (x : P) : x ∈ S := by
  let inl' : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S hA)
  let inr' : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hB)
  have w : φ ≫ inl' = ψ ≫ inr' := by
    ext r
    exact congrArg (fun g => g.hom r) H.w
  have hd : H.desc inl' inr' w ≫ CommRingCat.ofHom S.subtype = 𝟙 P := by
    apply H.hom_ext
    · rw [H.inl_desc_assoc, Category.comp_id]; rfl
    · rw [H.inr_desc_assoc, Category.comp_id]; rfl
  have := congrArg (fun g => g.hom x) hd
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  rw [← this]
  exact ((H.desc inl' inr' w).hom x).2

theorem isClosed_basicOpen_idem {Y : Scheme.{0}} {e : Γ(Y, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (Y.basicOpen e : Set Y) := by
  have : (Y.basicOpen e : Set Y) = (Y.basicOpen (1 - e) : Set Y)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ Y.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Y.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (Y.mem_basicOpen e x trivial).2 h'
      · exact absurd ((Y.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (Y.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory.GeomConnDesc

end

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

variable {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Sp F) {K : Type} [Field K] (i₀ : F →+* K)

def Lc {n : ℕ} (c : Fin n → K) : Subfield K := Subfield.closure (Set.range i₀ ∪ Set.range c)

theorem mem_Lc {n : ℕ} (c : Fin n → K) (x : F) : i₀ x ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inl ⟨x, rfl⟩)

theorem mem_Lc' {n : ℕ} (c : Fin n → K) (k : Fin n) : c k ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inr ⟨k, rfl⟩)

theorem hji_L (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) : L.subtype.comp (i₀.codRestrict L hL) = i₀ :=
  RingHom.ext fun _ => rfl

def hcL (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict L hL)) :=
  bc f i₀ (i₀.codRestrict L hL) L.subtype (hji_L i₀ L hL)

theorem hcL_factor {L₁ L₂ : Subfield K} (hL₁ : ∀ x, i₀ x ∈ L₁) (hL₂ : ∀ x, i₀ x ∈ L₂) (hle : L₁ ≤ L₂)
    (y : Γ(pullback f (spMap (i₀.codRestrict L₁ hL₁)), ⊤)) :
    ∃ y', (hcL f i₀ L₁ hL₁).appTop.hom y = (hcL f i₀ L₂ hL₂).appTop.hom y' := by
  have e : hcL f i₀ L₁ hL₁ = hcL f i₀ L₂ hL₂ ≫ bc f (i₀.codRestrict L₂ hL₂)
      (i₀.codRestrict L₁ hL₁) (Subfield.inclusion hle) (RingHom.ext fun _ => rfl) :=
    bc_trans f i₀ (i₀.codRestrict L₁ hL₁) L₁.subtype (hji_L i₀ L₁ hL₁)
      (i₀.codRestrict L₂ hL₂) L₂.subtype (hji_L i₀ L₂ hL₂) (Subfield.inclusion hle)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
  exact ⟨_, by rw [e, appTop_comp_apply]⟩

def hc {n : ℕ} (c : Fin n → K) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))) :=
  hcL f i₀ (Lc i₀ c) (mem_Lc i₀ c)

theorem hc_factor {n m : ℕ} (c : Fin n → K) (d : Fin m → K) (hle : Lc i₀ c ≤ Lc i₀ d)
    (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)) :
    ∃ y', (hc f i₀ c).appTop.hom y = (hc f i₀ d).appTop.hom y' :=
  hcL_factor f i₀ (mem_Lc i₀ c) (mem_Lc i₀ d) hle y

theorem Lc_le_append_left {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ c ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.castAdd m k, Fin.append_left _ _ _⟩))

theorem Lc_le_append_right {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ d ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.natAdd n k, Fin.append_right _ _ _⟩))

theorem gen [QuasiCompact f] [QuasiSeparated f] (x : Γ(pullback f (spMap i₀), ⊤)) :
    ∃ (n : ℕ) (c : Fin n → K) (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)),
      (hc f i₀ c).appTop.hom y = x := by
  haveI : Flat (spMap i₀) := flat_spec_field _
  let S : Subring Γ(pullback f (spMap i₀), ⊤) :=
    { carrier := {x | ∃ (n : ℕ) (c : Fin n → K)
        (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)), (hc f i₀ c).appTop.hom y = x}
      zero_mem' := ⟨0, Fin.elim0, 0, map_zero _⟩
      one_mem' := ⟨0, Fin.elim0, 1, map_one _⟩
      neg_mem' := by
        rintro _ ⟨n, c, y, rfl⟩
        exact ⟨n, c, -y, map_neg _ _⟩
      add_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' + z', by rw [map_add, hy', hz']⟩
      mul_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' * z', by rw [map_mul, hy', hz']⟩ }
  have H := ProperFunctions.isPushout_appTop (IsPullback.of_hasPullback f (spMap i₀))
  refine mem_of_isPushout H S (fun a => ?_) (fun b => ?_) x
  · refine ⟨0, Fin.elim0, (pullback.fst f _).appTop.hom a, ?_⟩
    rw [← appTop_comp_apply]
    exact congrArg (fun g => g.appTop.hom a) (bc_fst f i₀ (i₀.codRestrict (Lc i₀ Fin.elim0) (mem_Lc i₀ Fin.elim0)) (Lc i₀ Fin.elim0).subtype (hji_L i₀ _ (mem_Lc i₀ Fin.elim0)))
  · let c : Fin 1 → K := ![(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b]
    refine ⟨1, c, (pullback.snd f _).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Lc i₀ c))).inv.hom ⟨c 0, mem_Lc' i₀ c 0⟩), ?_⟩
    rw [← appTop_comp_apply]
    rw [show hc f i₀ c ≫ pullback.snd f _ = pullback.snd f (spMap i₀) ≫ spMap (Lc i₀ c).subtype from
      bc_snd f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)), appTop_comp_apply, appTop_spMap_inv]
    change (pullback.snd f (spMap i₀)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b)) = _
    simp

theorem preconnectedSpace_of_finGen : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F),
    QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  intro F _ X f _ _ K _ i₀ hyp
  haveI : Flat f := flat_spec_field f
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ U hU
  obtain ⟨n, c, y, rfl⟩ := gen f i₀ e
  have hinj : Function.Injective (hc f i₀ c).appTop.hom :=
    ProperFunctions.injective_appTop_of_isPullback (isPullback_bc f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)))
      (appTop_spMap_injective _ (Lc i₀ c).subtype.injective)
  have hy : IsIdempotentElem y := hinj (by rw [map_mul]; exact he)
  have hcl : IsClopen (SetLike.coe (Scheme.basicOpen _ y)) :=
    ⟨isClosed_basicOpen_idem hy, (Scheme.basicOpen _ y).isOpen⟩
  haveI := hyp (Lc i₀ c) (mem_Lc i₀ c) n c rfl
  have hU' : U = (hc f i₀ c) ⁻¹' (SetLike.coe (Scheme.basicOpen _ y)) := by
    rw [← hUe, ← Scheme.preimage_basicOpen_top]; rfl
  rcases isClopen_iff.1 hcl with h0 | h1
  · left; rw [hU', h0]; rfl
  · right; rw [hU', h1]; rfl

end GlobalTheory.GeomConnDesc

end
