import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacquetBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_surjective {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]

omit [LinearOrder α] in

theorem leviEmb_apply_of_blk_ne (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne R e g (by simpa using h) x y

theorem leviEmb_leviProj_of_blk (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviProj_apply]
  · rw [leviEmb_apply_ne R e _ hab, h _ _ (by simpa using hab)]

theorem leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  rcases p with ⟨p, hp⟩
  simp only at h
  subst h
  exact leviProj_leviEmb R e g

end Blocks

section Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_of_transport (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h

end Transport

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_reindex (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    obtain ⟨⟨a, x⟩, rfl⟩ := (e.trans ψ).surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := (e.trans ψ).surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, MonoidHom.id_apply]
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨a, y⟩) = (e.trans ψ) ⟨a, y⟩ from rfl, leviEmb_apply_same]
    · rw [leviEmb_apply_ne k e _ hab, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨b, y⟩) = (e.trans ψ) ⟨b, y⟩ from rfl, leviEmb_apply_ne k _ _ hab]

theorem hasFiniteLength_jacU_relabel (e : (Σ a, m a) ≃ n) (s : (Σ b, m' b) ≃ (Σ a, m a))
    (f : β → α) (hf : StrictMono f) (hs : ∀ x, (s x).1 = f x.1) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU (s.trans e) π)) : HasFiniteLength (jacU e π) := by
  set e₁ := s.trans e
  have hblk : ∀ i, blk e i = f (blk e₁ i) := fun i => by
    have := hs (s.symm (e.symm i))
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hlt : ∀ i j, blk e i < blk e j ↔ blk e₁ i < blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.lt_iff_lt]
  have heq : ∀ i j, blk e i = blk e j ↔ blk e₁ i = blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.injective.eq_iff]
  have hpar : ∀ g : GL n k, g ∈ parab k e ↔ g ∈ parab k e₁ := fun g => by
    rw [mem_parab, mem_parab]
    exact forall_congr' fun i => forall_congr' fun j => by rw [hlt]
  let Ψ : Levi k m' →* Levi k m := (leviProj k e).comp ((leviEmb k e₁).codRestrict (parab k e)
    fun g => (hpar _).2 (leviEmb_mem_parab k e₁ g))
  have hL : ∀ g, leviEmb k e₁ g = leviEmb k e (Ψ g) := fun g => by
    refine (leviEmb_leviProj_of_blk (R := k) e ⟨leviEmb k e₁ g, (hpar _).2 (leviEmb_mem_parab k e₁ g)⟩
      fun i j hij => ?_).symm
    exact leviEmb_apply_of_blk_ne e₁ g fun h' => hij ((heq i j).2 h')
  have hΨ : Function.Surjective Ψ := by
    intro g
    refine ⟨leviProj k e₁ ⟨leviEmb k e g, (hpar _).1 (leviEmb_mem_parab k e g)⟩, ?_⟩
    refine leviProj_eq_of_coe_eq (R := k) e _ g ?_
    exact leviEmb_leviProj_of_blk (R := k) e₁ _ fun i j hij =>
      leviEmb_apply_of_blk_ne e g fun h' => hij ((heq i j).1 h')
  refine hasFiniteLength_jacU_of_transport e e₁ (MonoidHom.id _) Ψ hΨ (fun u hu => ?_)
    (fun g => hL g) π h
  rw [mem_unipRad_iff_blk] at hu ⊢
  exact ⟨(hpar _).2 hu.1, fun i j hij => hu.2 i j ((heq i j).1 hij)⟩

end Stages

theorem jacquetFiniteLength_of_standard :
    GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  intro hP k _ _ _ _ α n m _ _ _ _ _ _ e V _ _ π hπ hl
  classical
  let α' := {a : α // Nonempty (m a)}
  let o : Fin (Fintype.card α') ≃o α' := monoEquivOfFin α' rfl
  let d : Fin (Fintype.card α') → ℕ := fun i => Fintype.card (m (o i).1)
  have hd : ∀ i, 0 < d i := fun i => Fintype.card_pos_iff.2 (o i).2
  let T : (Σ a' : α', m a'.1) ≃ (Σ a, m a) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, ⟨x.2⟩⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let s : (Σ i, Fin (d i)) ≃ (Σ a, m a) :=
    ((Equiv.sigmaCongrRight fun i => (Fintype.equivFin (m (o i).1)).symm).trans
      (Equiv.sigmaCongrLeft (β := fun a' : α' => m a'.1) o.toEquiv)).trans T
  have hs : ∀ x, (s x).1 = (fun i => (o i).1) x.1 := by
    rintro ⟨i, j⟩
    rfl
  have hf : StrictMono (fun i => (o i).1) := fun i j h => o.strictMono h
  let e₁ := s.trans e
  let ψ : Fin (∑ i, d i) ≃ n := finSigmaFinEquiv.symm.trans e₁
  let Φ : GL (Fin (∑ i, d i)) k →* GL n k :=
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦs : Function.Surjective Φ := (Units.mapEquiv _).surjective
  have hΦc : Continuous Φ := by
    refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · exact Units.continuous_val.matrix_elem (ψ.symm i) (ψ.symm j)
    · exact Units.continuous_coe_inv.matrix_elem (ψ.symm i) (ψ.symm j)
  have h1 := (hP k _ d hd).1 V (π.comp Φ) (isSmooth_comp hπ Φ hΦc)
    ((hasFiniteLength_comp_iff π Φ hΦs).2 hl)
  have h2 : HasFiniteLength (jacU (finSigmaFinEquiv.trans ψ) π) :=
    hasFiniteLength_jacU_reindex _ ψ π
      ((hasFiniteLength_twist_iff (jacU finSigmaFinEquiv (π.comp Φ)) _).1 h1)
  have he : finSigmaFinEquiv.trans ψ = e₁ := by
    ext x
    simp [ψ]
  rw [he] at h2
  exact (hasFiniteLength_twist_iff (jacU e π) (deltaHalf k m)⁻¹).2
    (hasFiniteLength_jacU_relabel e s _ hf hs π h2)

end GlobalTheory.JacquetBlocks

end
