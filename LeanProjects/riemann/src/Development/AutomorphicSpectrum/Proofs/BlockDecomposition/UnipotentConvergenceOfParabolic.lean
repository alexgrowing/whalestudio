import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv

open PositivityTheory.RgEis

variable {G : Type} [Group G]

theorem cos_mk_eq_iff {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by
  constructor
  · intro h
    have h1 : b * a⁻¹ ∈ P.subgroupOf Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using Subgroup.mem_subgroupOf.mp h1
  · intro h
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simpa using h

theorem cos_eq_of_rep {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by
  have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) (Quotient.out q) (Quotient.out q')).mpr h
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  exact h'

theorem rep_mk {P Γ : Subgroup G} (a : Γ) :
    ∃ p ∈ Γ, p ∈ P ∧ rep (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = p * a := by
  refine ⟨rep (Quotient.mk _ a : Cos P Γ) * (a : G)⁻¹, ?_, ?_, ?_⟩
  · exact Γ.mul_mem (Quotient.out (Quotient.mk _ a : Cos P Γ)).2 (Γ.inv_mem a.2)
  · exact (cos_mk_eq_iff (P := P) (Γ := Γ) a (Quotient.out (Quotient.mk _ a : Cos P Γ))).mp
      (Quotient.out_eq _).symm
  · exact (inv_mul_cancel_right _ _).symm

theorem conv_comap {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by
  intro g'
  have hinj : Function.Injective (fun q' : Cos P' Γ' =>
      (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ)) := by
    intro q₁ q₂ h
    have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) _ _).mp h
    apply cos_eq_of_rep
    have hmem : rep q₂ * (rep q₁)⁻¹ ∈ Γ' :=
      Γ'.mul_mem (Quotient.out q₂).2 (Γ'.inv_mem (Quotient.out q₁).2)
    refine hP _ hmem ?_
    rw [map_mul, map_inv]
    exact h'
  refine ((hc (φ g')).comp_injective hinj).congr fun q' => ?_
  obtain ⟨p, hpΓ, hpP, hp⟩ := rep_mk (P := P) (Γ := Γ) ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩
  show Real.exp (l (rep (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ) * φ g')) =
    Real.exp (l (φ (rep q' * g')))
  rw [hp, map_mul, mul_assoc, hl p hpΓ hpP]

theorem conv_inf {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by
  intro g
  have hinj : Function.Injective (fun q : Cos (P₁ ⊓ P₂) Γ =>
      ((Quotient.mk _ (Quotient.out q) : Cos P₁ Γ), (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ))) := by
    intro q q' h
    have e1 := (cos_mk_eq_iff (P := P₁) (Γ := Γ) _ _).mp (congrArg Prod.fst h)
    have e2 := (cos_mk_eq_iff (P := P₂) (Γ := Γ) _ _).mp (congrArg Prod.snd h)
    exact cos_eq_of_rep (Subgroup.mem_inf.mpr ⟨e1, e2⟩)
  have hprod : Summable fun x : Cos P₁ Γ × Cos P₂ Γ =>
      Real.exp (l₁ (rep x.1 * g)) * Real.exp (l₂ (rep x.2 * g)) := by
    exact Summable.mul_of_nonneg (c₁ g) (c₂ g) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  refine (hprod.comp_injective hinj).congr fun q => ?_
  obtain ⟨p₁, hp₁Γ, hp₁P, hp₁⟩ := rep_mk (P := P₁) (Γ := Γ) (Quotient.out q)
  obtain ⟨p₂, hp₂Γ, hp₂P, hp₂⟩ := rep_mk (P := P₂) (Γ := Γ) (Quotient.out q)
  show Real.exp (l₁ (rep (Quotient.mk _ (Quotient.out q) : Cos P₁ Γ) * g)) *
      Real.exp (l₂ (rep (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ) * g)) =
    Real.exp (l₁ (rep q * g) + l₂ (rep q * g))
  rw [hp₁, hp₂, mul_assoc, mul_assoc, h₁ p₁ hp₁Γ hp₁P, h₂ p₂ hp₂Γ hp₂P, Real.exp_add]
  rfl

theorem convU_of_parLaw : ParLaw → ConvU := by
  intro hPar E R _ _ _ _ _ _ _ A hA hGr ι _ _ ε s hIwa
  have inv : ∀ {H : Type} [Group H] [TopologicalSpace H] {Γ K P : Subgroup H} {η : H → ℝ} (c : ℝ),
      IsHt Γ K P η → ∀ γ ∈ Γ, γ ∈ P → ∀ g, c * η (γ * g) = c * η g := by
    intro H _ _ Γ K P η c h γ hγ hγP g
    rw [h.left γ hγP g, h.rat γ hγ hγP, zero_add]
  have hconv : ∀ (t : Set ι) (x : ℝ), (∀ g : A.U ε ι, A.uH ε t g = A.htGL (Sum.inl '' t) g.1) →
      IsHt (A.ratGL (ι ⊕ ι)) (A.kGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (A.htGL (Sum.inl '' t)) →
      Conv (A.ratGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (fun g => x * A.htGL (Sum.inl '' t) g) →
      Conv (A.uΓ ε ι) (A.uQ ε t) fun g => x * A.uH ε t g := by
    intro t x heq hHt hc
    have h := conv_comap (A.uSub ε ι).subtype (Γ := A.ratGL (ι ⊕ ι)) (P := stab R (Sum.inl '' t))
      (Γ' := A.uΓ ε ι) (P' := A.uQ ε t) (l := fun g => x * A.htGL (Sum.inl '' t) g)
      (fun γ hγ => Subgroup.mem_subgroupOf.mp hγ) (fun γ _ hγ => Subgroup.mem_subgroupOf.mpr hγ)
      (inv x hHt) hc
    have hfun : (fun g : A.U ε ι => x * A.uH ε t g) =
        fun g => x * A.htGL (Sum.inl '' t) ((A.uSub ε ι).subtype g) := by
      funext g
      exact congrArg (fun r => x * r) (heq g)
    rw [hfun]
    exact h
  have hIwaU : Iwa (A.uQ ε (Set.univ : Set ι) ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
    intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hIwa g
    exact ⟨p, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hp).2, (Subgroup.mem_inf.mp hp).2⟩, k, hk, hg⟩
  obtain ⟨Rs, hRs⟩ := hGr (ι ⊕ ι) (Sum.inl '' s)
  obtain ⟨Ru, hRu⟩ := hGr (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  have hs := (hPar E R A hA ι ε s).2 hIwa
  have hu := (hPar E R A hA ι ε Set.univ).2 hIwaU
  have hGs := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' s)).1.2.2.2.1
  have hGu := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' (Set.univ : Set ι))).1.2.2.2.1
  refine ⟨max Rs Ru, fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy))
  · exact conv_inf (l₁ := fun g => x * A.uH ε s g) (l₂ := fun g => y * A.uH ε Set.univ g)
      (inv x hs.2.1) (inv y hu.2.1)
      (hconv s x hs.2.2 hGs (hRs x (lt_of_le_of_lt (le_max_left _ _) hx)))
      (hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy)))

end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
