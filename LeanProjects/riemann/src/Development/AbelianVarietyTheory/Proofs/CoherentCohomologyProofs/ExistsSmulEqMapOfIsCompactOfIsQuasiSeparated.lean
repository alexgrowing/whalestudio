import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Glue

variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)

theorem exists_smul_eq_zero_of_isCompact
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hbot : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (a : A W) (ha : φ W a = 0) :
    ∃ s ∈ S, s • a = 0 := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → ∀ a : A ⟨W, h⟩,
      φ ⟨W, h⟩ a = 0 → ∃ s ∈ S, s • a = 0) W hW ?_ ?_ hWU hW a ha
  · intro h _ a _
    have := hbot ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ a ha
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, e₁⟩ := ih T'.2 hT (rA h₁ a) (by rw [hφ, ha, map_zero])
    obtain ⟨s₂, hs₂, e₂⟩ := hker V' V.2 (rA h₂ a) (by rw [hφ, ha, map_zero])
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, sepA h₁ h₂ le_rfl _ ?_ ?_⟩
    · rw [map_smul, mul_comm, mul_smul, e₁, smul_zero]
    · rw [map_smul, mul_smul, e₂, smul_zero]

theorem exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hrB : ∀ {V₁ V₂ V₃} (h : V₁ ≤ V₂) (h' : V₂ ≤ V₃) (b : B V₃),
      rB h (rB h' b) = rB (h.trans h') b)
    (hbotA : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (hbotB : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (B V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (sepB : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ b : B W, rB h₁ b = 0 → rB h₂ b = 0 → b = 0)
    (glueA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ (a₁ : A V₁) (a₂ : A V₂), rA (inf_le_left : V₁ ⊓ V₂ ≤ V₁) a₁ = rA inf_le_right a₂ →
        ∃ a : A W, rA h₁ a = a₁ ∧ rA h₂ a = a₂)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (hsurj : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ b : B V, ∃ s ∈ S, ∃ a : A V, s • b = φ V a)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (hW' : IsQuasiSeparated (W.1 : Set X))
    (b : B W) : ∃ s ∈ S, ∃ a : A W, s • b = φ W a := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → IsQuasiSeparated (W : Set X) →
      ∀ b : B ⟨W, h⟩, ∃ s ∈ S, ∃ a : A ⟨W, h⟩, s • b = φ ⟨W, h⟩ a) W hW ?_ ?_ hWU hW hW' b
  · intro h _ _ b
    have := hbotB ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, 0, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ hqs b
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := ih T'.2 hT (hqs.of_subset Set.subset_union_left) (rB h₁ b)
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := hsurj V' V.2 (rB h₂ b)
    have hc : IsCompact ((T' ⊓ V').1 : Set X) :=
      hqs _ _ Set.subset_union_left T.2 hT Set.subset_union_right V.1.2 V.2.isCompact
    obtain ⟨s, hs, e⟩ := exists_smul_eq_zero_of_isCompact S U rA rB φ hφ hbotA sepA hker
      (T' ⊓ V') hc (s₂ • rA inf_le_left a₁ - s₁ • rA inf_le_right a₂) (by
        rw [map_sub, map_smul, map_smul, hφ, hφ, ← e₁, ← e₂, map_smul, map_smul, hrB, hrB,
          smul_comm, sub_self])
    obtain ⟨a, ha₁, ha₂⟩ := glueA h₁ h₂ le_rfl (s • s₂ • a₁) (s • s₁ • a₂) (by
      rw [smul_sub, sub_eq_zero] at e
      simpa only [map_smul] using e)
    refine ⟨s * (s₁ * s₂), mul_mem hs (mul_mem hs₁ hs₂), a, ?_⟩
    rw [← sub_eq_zero]
    refine sepB h₁ h₂ le_rfl _ ?_ ?_
    · rw [map_sub, ← hφ, ha₁, map_smul, map_smul, map_smul, ← e₁, mul_comm s₁, mul_smul, mul_smul,
        sub_self]
    · rw [map_sub, ← hφ, ha₂, map_smul, map_smul, map_smul, ← e₂, mul_smul, mul_smul, sub_self]

end Glue

section Sheaf

variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}

theorem subsingleton_sections_of_eq_bot (h : W = ⊥) : Subsingleton Γ(F, W) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{u + 1} ↦ i.elim) W (fun i ↦ i.elim) (by simp [h]) s t (fun i ↦ i.elim)

theorem section_eq_zero_of_res₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s : Γ(F, W))
    (e₁ : F.presheaf.map (homOfLE h₁).op s = 0) (e₂ : F.presheaf.map (homOfLE h₂).op s = 0) :
    s = 0 :=
  TopCat.Sheaf.eq_of_locally_eq₂ (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ (homOfLE h₁) (homOfLE h₂)
    h s 0 (e₁.trans (map_zero _).symm) (e₂.trans (map_zero _).symm)

theorem exists_section_glue₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s₁ : Γ(F, V₁))
    (s₂ : Γ(F, V₂))
    (e : F.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.presheaf.map (homOfLE inf_le_right).op s₂) :
    ∃ s : Γ(F, W), F.presheaf.map (homOfLE h₁).op s = s₁ ∧
      F.presheaf.map (homOfLE h₂).op s = s₂ := by
  let 𝒰 : Bool → X.Opens := fun b ↦ Bool.rec V₁ V₂ b
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    𝒰 W (fun b ↦ Bool.rec (homOfLE h₁) (homOfLE h₂) b)
    (h.trans (sup_le (le_iSup 𝒰 false) (le_iSup 𝒰 true)))
    (fun b ↦ Bool.rec s₁ s₂ b) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact e
      · have := congr(F.presheaf.map (homOfLE (inf_comm V₂ V₁).le).op $e)
        rw [res_res, res_res] at this
        exact this.symm
      · rfl)
  exact ⟨s, hs false, hs true⟩

end Sheaf

section BasicOpen

variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

def resLinearOver (hW : W ≤ U) (hV : V ≤ U) (h : V ≤ W) :
    letI := resModule F hW
    letI := resModule F hV
    Γ(F, W) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F hW
  letI := resModule F hV
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ by
      rw [resModule_smul, F.map_smul, res_res_ring]; rfl }

variable [F.IsQuasicoherent]

theorem exists_pow_smul_eq_zero_of_isCompact (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : V ≤ U) (hV : V = X.basicOpen f) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE h).op t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := exists_smul_eq_zero_of_isCompact (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU t (by
      change F.presheaf.map (homOfLE inf_le_left).op t = 0
      rw [← res_res F h inf_le_right, ht, map_zero])
  refine ⟨n, ?_⟩
  rw [← res_self_ring le_rfl (f ^ n)]
  exact e

theorem exists_pow_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f)
    (s : Γ(F, V)) : ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, t, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun h₁ h₂ b ↦ res_res F _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F (by simp [hW]))
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F (inf_le_inf_right V h₁) (inf_le_inf_right V h₂)
      ((inf_le_inf_right V h₃).trans (inf_sup_right _ _ _).le))
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    (fun W hW b ↦ by
      obtain ⟨n, a, hn⟩ := exists_pow_smul_eq_res F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        (V := W.1 ⊓ V) inf_le_left (by rw [X.basicOpen_res, hV]) b
      exact ⟨f ^ n, ⟨n, rfl⟩, a, by rw [res_res_ring (show W.1 ≤ U from W.2), ← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU hU' (F.presheaf.map (homOfLE inf_le_right).op s)
  refine ⟨n, t, ?_⟩
  have e' : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (f ^ n) •
      F.presheaf.map (homOfLE inf_le_right).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := e
  have := congr(F.presheaf.map (homOfLE (le_inf h le_rfl)).op $e')
  rwa [F.map_smul, res_res, res_res, res_res_ring, res_self, map_pow] at this

theorem isLocalizedModule_resBasicOpen_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isLocalizedModule_resBasicOpen_iff F f).mpr
    ⟨exists_pow_smul_eq_res_of_qcqs F hU hU' f _ rfl,
      exists_pow_smul_eq_zero_of_isCompact F hU f _ rfl⟩

theorem isLocalizedModule_of_ringHom_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) {A : Type*} [CommRing A]
    (φ : A →+* Γ(X, U)) (a : A) (h : V ≤ U) (hV : V = X.basicOpen (φ a))
    [Module A Γ(F, U)] [Module A Γ(F, V)]
    (hsU : ∀ (r : A) (s : Γ(F, U)), r • s = φ r • s)
    (hsV : ∀ (r : A) (s : Γ(F, V)), r • s = X.presheaf.map (homOfLE h).op (φ r) • s)
    (l : Γ(F, U) →ₗ[A] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsLocalizedModule.Away a l := by
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun s ↦ ?_) (fun t ht ↦ ?_)
  · have := (isUnit_res_of_le_basicOpen (φ a) h hV.le).map
      (algebraMap Γ(X, V) (Module.End Γ(X, V) Γ(F, V)))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    ext s
    exact hsV a s
  · obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res_of_qcqs F hU hU' (φ a) h hV s
    exact ⟨n, t, by rw [hsV, hl, map_pow, map_pow, ht]⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isCompact F hU (φ a) h hV t (by rw [← hl, ht])
    exact ⟨n, by rw [hsU, map_pow, hn]⟩

theorem isLocalizedModule_resBasicOpen_top [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) : IsLocalizedModule.Away f (resBasicOpen F f) :=
  isLocalizedModule_resBasicOpen_of_qcqs F isCompact_univ (isQuasiSeparated_univ) f

end BasicOpen

section Hom

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}

theorem app_res (h : V ≤ W) (s : Γ(F, W)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ.app W s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)

def appLinearOver (h : V ≤ U) :
    letI := resModule F h
    letI := resModule G h
    Γ(F, V) →ₗ[Γ(X, U)] Γ(G, V) :=
  letI := resModule F h
  letI := resModule G h
  { toFun := φ.app V
    map_add' := map_add _
    map_smul' := fun _ s ↦ φ.app_smul _ s }

theorem exists_smul_eq_zero_of_app_eq_zero (hU : IsCompact (U : Set X)) (S : Submonoid Γ(X, U))
    (hker : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ a : Γ(F, V), φ.app V a = 0 →
      ∃ s ∈ S, X.presheaf.map (homOfLE h).op s • a = 0)
    (a : Γ(F, U)) (ha : φ.app U a = 0) : ∃ s ∈ S, s • a = 0 := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(G, W.1) := resModule G W.2
  obtain ⟨s, hs, e⟩ := exists_smul_eq_zero_of_isCompact S U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(G, W.1))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver G W₂.2 W₁.2 h')
    (fun W ↦ appLinearOver φ W.2)
    (fun h' a ↦ app_res φ h' a)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun W hW ↦ hker W.1 W.2 hW) ⟨U, Set.self_mem_Iic⟩ hU a ha
  refine ⟨s, hs, ?_⟩
  rw [← res_self_ring le_rfl s]
  exact e

theorem exists_smul_eq_app (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (S : Submonoid Γ(X, U))
    (hker : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ a : Γ(F, V), φ.app V a = 0 →
      ∃ s ∈ S, X.presheaf.map (homOfLE h).op s • a = 0)
    (hsurj : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ b : Γ(G, V),
      ∃ s ∈ S, ∃ a : Γ(F, V), X.presheaf.map (homOfLE h).op s • b = φ.app V a)
    (b : Γ(G, U)) : ∃ s ∈ S, ∃ a : Γ(F, U), s • b = φ.app U a := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(G, W.1) := resModule G W.2
  obtain ⟨s, hs, a, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated S U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(G, W.1))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver G W₂.2 W₁.2 h')
    (fun W ↦ appLinearOver φ W.2)
    (fun h' a ↦ app_res φ h' a)
    (fun h₁ h₂ b ↦ res_res G _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot G hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ G h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW ↦ hker W.1 W.2 hW) (fun W hW ↦ hsurj W.1 W.2 hW) ⟨U, Set.self_mem_Iic⟩ hU hU' b
  refine ⟨s, hs, a, ?_⟩
  rw [← res_self_ring le_rfl s]
  exact e

end Hom

end GlobalTheory.QCoh.Qcqs
