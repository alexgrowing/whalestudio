import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSat2InvTConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open GlobalTheory.BCT

namespace GlobalTheory.CompanionTheory.ActTr

section Hint

variable {Γ Γ' : Type} [Group Γ] [Group Γ']

theorem hint_const_mul (K : Subgroup Γ) (u : Γ → ℂ) (c : ℂ) :
    hint K (fun x => c * u x) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simp [GlobalTheory.CompanionTheory.FamClP.hint_zero]
  · have hs : rStab (fun x => c * u x) = rStab u := by
      ext r
      simp only [GlobalTheory.CompanionTheory.FamClP.mem_rStab']
      constructor
      · intro h x
        exact mul_left_cancel₀ hc (h x)
      · intro h x
        rw [h x]
    unfold hint
    rw [hs, mul_left_comm, ← smul_eq_mul c (∑ᶠ _ : Γ ⧸ (rStab u ⊓ K), _), smul_finsum]
    rfl

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']

theorem relIndex_ne_zero {K L : Subgroup Γ} (hK : IsCompact (K : Set Γ)) (hL : IsOpen (L : Set Γ)) :
    L.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hL.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen (L.subgroupOf K) ho
  exact Subgroup.index_ne_zero_of_finite

theorem hint_lin {K L : Subgroup Γ} {C : Set Γ} (hK : IsCompact (K : Set Γ)) (hL : IsOpen (L : Set Γ)) (hLK : L ≤ K)
    (hC : IsCompact C) : ∃ (T : Finset (Γ ⧸ L)) (c : ℂ), ∀ u : Γ → ℂ, (∀ l ∈ L, ∀ x, u (x * l) = u x) →
      (∀ x, u x ≠ 0 → x ∈ C) → hint K u = c * ∑ q ∈ T, u q.out := by
  haveI : DiscreteTopology (Γ ⧸ L) := QuotientGroup.discreteTopology hL
  have hf : ((QuotientGroup.mk : Γ → Γ ⧸ L) '' C).Finite :=
    (hC.image QuotientGroup.continuous_mk).finite_of_discrete
  refine ⟨hf.toFinset, ((L.relIndex K : ℕ) : ℂ)⁻¹, fun u hu hs => ?_⟩
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K L u hLK (fun l hl x => hu l hl x) (relIndex_ne_zero hK hL)]
  congr 1
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  simp only [Set.Finite.coe_toFinset]
  exact ⟨q.out, hs _ hq, QuotientGroup.out_eq' q⟩

theorem hint_comm {K₁ L₁ : Subgroup Γ} {K₂ L₂ : Subgroup Γ'} {C₁ : Set Γ} {C₂ : Set Γ'}
    (hK₁ : IsCompact (K₁ : Set Γ)) (hL₁ : IsOpen (L₁ : Set Γ)) (hLK₁ : L₁ ≤ K₁) (hC₁ : IsCompact C₁)
    (hK₂ : IsCompact (K₂ : Set Γ')) (hL₂ : IsOpen (L₂ : Set Γ')) (hLK₂ : L₂ ≤ K₂) (hC₂ : IsCompact C₂)
    (F : Γ → Γ' → ℂ) (h₁ : ∀ l ∈ L₁, ∀ x y, F (x * l) y = F x y) (h₂ : ∀ l ∈ L₂, ∀ x y, F x (y * l) = F x y)
    (hs : ∀ x y, F x y ≠ 0 → x ∈ C₁ ∧ y ∈ C₂) :
    hint K₁ (fun x => hint K₂ (F x)) = hint K₂ (fun y => hint K₁ fun x => F x y) := by
  obtain ⟨T₁, c₁, e₁⟩ := hint_lin hK₁ hL₁ hLK₁ hC₁
  obtain ⟨T₂, c₂, e₂⟩ := hint_lin hK₂ hL₂ hLK₂ hC₂
  have i₂ : ∀ x, hint K₂ (F x) = c₂ * ∑ q ∈ T₂, F x q.out := fun x =>
    e₂ _ (fun l hl y => h₂ l hl x y) fun y hy => (hs x y hy).2
  have i₁ : ∀ y, hint K₁ (fun x => F x y) = c₁ * ∑ q ∈ T₁, F q.out y := fun y =>
    e₁ _ (fun l hl x => h₁ l hl x y) fun x hx => (hs x y hx).1
  have o₁ : hint K₁ (fun x => hint K₂ (F x)) = c₁ * ∑ q ∈ T₁, hint K₂ (F q.out) := by
    refine e₁ (fun x => hint K₂ (F x)) (fun l hl x => ?_) fun x hx => ?_
    · exact congrArg (hint K₂) (funext fun y => h₁ l hl x y)
    · by_contra hn
      refine hx ?_
      have : F x = fun _ => (0 : ℂ) := funext fun y => by
        by_contra h0
        exact hn (hs x y h0).1
      show hint K₂ (F x) = 0
      rw [this, GlobalTheory.CompanionTheory.FamClP.hint_zero]
  have o₂ : hint K₂ (fun y => hint K₁ fun x => F x y) = c₂ * ∑ q ∈ T₂, hint K₁ (fun x => F x q.out) := by
    refine e₂ (fun y => hint K₁ fun x => F x y) (fun l hl y => ?_) fun y hy => ?_
    · exact congrArg (hint K₁) (funext fun x => h₂ l hl x y)
    · by_contra hn
      refine hy ?_
      have : (fun x => F x y) = fun _ => (0 : ℂ) := funext fun x => by
        by_contra h0
        exact hn (hs x y h0).2
      show hint K₁ (fun x => F x y) = 0
      rw [this, GlobalTheory.CompanionTheory.FamClP.hint_zero]
  rw [o₁, o₂]
  simp only [i₁, i₂, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
  ring

end Hint

section Act

variable {Γ Γ' Y P : Type} [Group Γ] [Group Γ'] [Group Y] [Group P]

def act (e : Γ →* Y) (K : Subgroup Γ) (f : Γ → ℂ) (G : Y → ℂ) : Y → ℂ :=
  fun z => hint K fun m => f m * G (z * e m)

def Sm [TopologicalSpace Γ] (e : Γ →* Y) (G : Y → ℂ) : Prop :=
  IsOpen (((rStab G).comap e : Subgroup Γ) : Set Γ)

theorem term_inv [TopologicalSpace Γ] {e : Γ →* Y} {A : Subgroup Γ} {f : Γ → ℂ} {G : Y → ℂ} (hf : IsHecke A f) (z : Y)
    {l : Γ} (hl : l ∈ A) (hG : e l ∈ rStab G) (x : Γ) : f (x * l) * G (z * e (x * l)) = f x * G (z * e x) := by
  rw [(hf.2 l hl x).2, map_mul, ← mul_assoc, hG]

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']

theorem term_supp {f : Γ → ℂ} {G : Y → ℂ} {e : Γ →* Y} {z : Y} (x : Γ) (h : f x * G (z * e x) ≠ 0) : x ∈ tsupport f :=
  subset_tsupport _ (left_ne_zero_of_mul h)

theorem act_add {e : Γ →* Y} {K A : Subgroup Γ} {f : Γ → ℂ} {G G' : Y → ℂ} (hK : IsCompact (K : Set Γ))
    (hKo : IsOpen (K : Set Γ)) (hA : IsOpen (A : Set Γ)) (hf : IsHecke A f) (hG : Sm e G) (hG' : Sm e G') (c : ℂ) :
    act e K f (G + c • G') = act e K f G + c • act e K f G' := by
  funext z
  let L : Subgroup Γ := A ⊓ (rStab G).comap e ⊓ (rStab G').comap e ⊓ K
  have hL : IsOpen (L : Set Γ) := ((hA.inter hG).inter hG').inter hKo
  obtain ⟨T, d, h⟩ := hint_lin hK hL (inf_le_right : L ≤ K) hf.1.isCompact
  have a1 := h (fun m => f m * G (z * e m)) (fun l hl x => term_inv hf z hl.1.1.1 hl.1.1.2 x) (fun x hx => term_supp x hx)
  have a2 := h (fun m => f m * G' (z * e m)) (fun l hl x => term_inv hf z hl.1.1.1 hl.1.2 x) (fun x hx => term_supp x hx)
  have a3 := h (fun m => f m * (G + c • G') (z * e m)) (fun l hl x => by
      have e1 := term_inv (e := e) hf z hl.1.1.1 hl.1.1.2 x
      have e2 := term_inv (e := e) hf z hl.1.1.1 hl.1.2 x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
      rw [e1, mul_left_comm, e2, mul_left_comm])
    (fun x hx => subset_tsupport _ (left_ne_zero_of_mul hx))
  show hint K (fun m => f m * (G + c • G') (z * e m)) = hint K (fun m => f m * G (z * e m)) + c * hint K (fun m => f m * G' (z * e m))
  rw [a1, a2, a3]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

theorem act_comm {e₁ : Γ →* Y} {e₂ : Γ' →* Y} {K₁ A₁ : Subgroup Γ} {K₂ A₂ : Subgroup Γ'} {f₁ : Γ → ℂ} {f₂ : Γ' → ℂ}
    {G : Y → ℂ} (hK₁ : IsCompact (K₁ : Set Γ)) (hKo₁ : IsOpen (K₁ : Set Γ)) (hA₁ : IsOpen (A₁ : Set Γ))
    (hK₂ : IsCompact (K₂ : Set Γ')) (hKo₂ : IsOpen (K₂ : Set Γ')) (hA₂ : IsOpen (A₂ : Set Γ'))
    (hf₁ : IsHecke A₁ f₁) (hf₂ : IsHecke A₂ f₂) (hG₁ : Sm e₁ G) (hG₂ : Sm e₂ G) (hc : ∀ x y, e₁ x * e₂ y = e₂ y * e₁ x) :
    act e₁ K₁ f₁ (act e₂ K₂ f₂ G) = act e₂ K₂ f₂ (act e₁ K₁ f₁ G) := by
  funext z
  let L₁ : Subgroup Γ := A₁ ⊓ (rStab G).comap e₁ ⊓ K₁
  let L₂ : Subgroup Γ' := A₂ ⊓ (rStab G).comap e₂ ⊓ K₂
  have hL₁ : IsOpen (L₁ : Set Γ) := (hA₁.inter hG₁).inter hKo₁
  have hL₂ : IsOpen (L₂ : Set Γ') := (hA₂.inter hG₂).inter hKo₂
  let F : Γ → Γ' → ℂ := fun x y => f₁ x * (f₂ y * G (z * e₁ x * e₂ y))
  have l : act e₁ K₁ f₁ (act e₂ K₂ f₂ G) z = hint K₁ (fun x => hint K₂ (F x)) := by
    show hint K₁ (fun m => f₁ m * hint K₂ (fun m' => f₂ m' * G (z * e₁ m * e₂ m'))) = _
    exact congrArg (hint K₁) (funext fun x => (hint_const_mul _ _ _).symm)
  have r : act e₂ K₂ f₂ (act e₁ K₁ f₁ G) z = hint K₂ (fun y => hint K₁ fun x => F x y) := by
    show hint K₂ (fun m' => f₂ m' * hint K₁ (fun m => f₁ m * G (z * e₂ m' * e₁ m))) = _
    refine congrArg (hint K₂) (funext fun y => ?_)
    rw [← hint_const_mul]
    refine congrArg (hint K₁) (funext fun x => ?_)
    show f₂ y * (f₁ x * G (z * e₂ y * e₁ x)) = f₁ x * (f₂ y * G (z * e₁ x * e₂ y))
    have e : z * e₂ y * e₁ x = z * e₁ x * e₂ y := by rw [mul_assoc, ← hc, ← mul_assoc]
    rw [e, mul_left_comm]
  rw [l, r]
  refine hint_comm hK₁ hL₁ inf_le_right hf₁.1.isCompact hK₂ hL₂ inf_le_right hf₂.1.isCompact F
    (fun l hl x y => ?_) (fun l hl x y => ?_) (fun x y h => ?_)
  · show f₁ (x * l) * (f₂ y * G (z * e₁ (x * l) * e₂ y)) = f₁ x * (f₂ y * G (z * e₁ x * e₂ y))
    have hl' : e₁ l ∈ rStab G := hl.1.2
    have e : z * e₁ (x * l) * e₂ y = z * e₁ x * e₂ y * e₁ l := by
      rw [map_mul]
      simp only [mul_assoc]
      rw [hc l y]
    rw [(hf₁.2 l hl.1.1 x).2, e, hl']
  · show f₁ x * (f₂ (y * l) * G (z * e₁ x * e₂ (y * l))) = f₁ x * (f₂ y * G (z * e₁ x * e₂ y))
    have hl' : e₂ l ∈ rStab G := hl.1.2
    have e : z * e₁ x * e₂ (y * l) = z * e₁ x * e₂ y * e₂ l := by simp only [map_mul, mul_assoc]
    rw [(hf₂.2 l hl.1.1 y).2, e, hl']
  · exact ⟨subset_tsupport _ (left_ne_zero_of_mul h),
      subset_tsupport _ (left_ne_zero_of_mul (right_ne_zero_of_mul h))⟩

theorem act_conv {e : Γ →* Y} {K A B : Subgroup Γ} {f g : Γ → ℂ} {G : Y → ℂ} (hK : IsCompact (K : Set Γ))
    (hKo : IsOpen (K : Set Γ)) (hA : IsOpen (A : Set Γ)) (hB : IsOpen (B : Set Γ)) (hf : IsHecke A f) (hg : IsHecke B g)
    (hG : Sm e G) :
    act e K (fun m => hint K fun m' => f m' * g (m'⁻¹ * m)) G = act e K f (act e K g G) := by
  funext z
  let L₁ : Subgroup Γ := A ⊓ B ⊓ K
  let L₂ : Subgroup Γ := B ⊓ (rStab G).comap e ⊓ K
  have hL₁ : IsOpen (L₁ : Set Γ) := (hA.inter hB).inter hKo
  have hL₂ : IsOpen (L₂ : Set Γ) := (hB.inter hG).inter hKo
  let F : Γ → Γ → ℂ := fun x y => f x * (g (x⁻¹ * y) * G (z * e y))
  have l : act e K (fun m => hint K fun m' => f m' * g (m'⁻¹ * m)) G z = hint K (fun y => hint K fun x => F x y) := by
    show hint K (fun m => (hint K fun m' => f m' * g (m'⁻¹ * m)) * G (z * e m)) = _
    refine congrArg (hint K) (funext fun y => ?_)
    rw [mul_comm, ← hint_const_mul]
    refine congrArg (hint K) (funext fun x => ?_)
    show G (z * e y) * (f x * g (x⁻¹ * y)) = f x * (g (x⁻¹ * y) * G (z * e y))
    ring
  have r : act e K f (act e K g G) z = hint K (fun x => hint K (F x)) := by
    show hint K (fun m => f m * hint K (fun m' => g m' * G (z * e m * e m'))) = _
    refine congrArg (hint K) (funext fun x => ?_)
    rw [← GlobalTheory.CompanionTheory.FamClP.hint_left K (fun m' => g m' * G (z * e x * e m')) x⁻¹, ← hint_const_mul]
    refine congrArg (hint K) (funext fun y => ?_)
    show f x * (g (x⁻¹ * y) * G (z * e x * e (x⁻¹ * y))) = f x * (g (x⁻¹ * y) * G (z * e y))
    have e' : z * e x * e (x⁻¹ * y) = z * e y := by simp [map_mul, mul_assoc]
    rw [e']
  rw [l, r]
  refine (hint_comm hK hL₁ inf_le_right hf.1.isCompact hK hL₂ inf_le_right (hf.1.isCompact.mul hg.1.isCompact) F
    (fun l hl x y => ?_) (fun l hl x y => ?_) (fun x y h => ?_)).symm
  · show f (x * l) * (g ((x * l)⁻¹ * y) * G (z * e y)) = f x * (g (x⁻¹ * y) * G (z * e y))
    have : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [(hf.2 l hl.1.1 x).2, this, (hg.2 l⁻¹ (inv_mem hl.1.2) _).1]
  · show f x * (g (x⁻¹ * (y * l)) * G (z * e (y * l))) = f x * (g (x⁻¹ * y) * G (z * e y))
    have hl' : e l ∈ rStab G := hl.1.2
    have e' : z * e (y * l) = z * e y * e l := by simp only [map_mul, mul_assoc]
    have e2 : x⁻¹ * (y * l) = x⁻¹ * y * l := (mul_assoc _ _ _).symm
    rw [e2, (hg.2 l hl.1.1 _).2, e', hl']
  · have h1 : f x ≠ 0 := left_ne_zero_of_mul h
    have h2 : g (x⁻¹ * y) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul h)
    exact ⟨subset_tsupport _ h1, Set.mem_mul.2 ⟨x, subset_tsupport _ h1, x⁻¹ * y, subset_tsupport _ h2, by group⟩⟩

def Lev [TopologicalSpace P] (fH : P →* Y) (G : Y → ℂ) : Prop :=
  ∃ U : Subgroup P, IsOpen (U : Set P) ∧ ∀ u ∈ U, ∀ x, G (x * fH u) = G x

variable [TopologicalSpace P] [IsTopologicalGroup P]

theorem sm_of_lev {fH : P →* Y} {ε : Γ →* P} (hε : Continuous ε) {G : Y → ℂ} (hG : Lev fH G) : Sm (fH.comp ε) G := by
  obtain ⟨U, hU, hUG⟩ := hG
  refine Subgroup.isOpen_mono (H₁ := U.comap ε) (fun l hl x => ?_) (hU.preimage hε)
  exact hUG _ hl x

theorem act_lev {fH : P →* Y} {ε : Γ →* P} (hε : Continuous ε) {K A : Subgroup Γ} {f : Γ → ℂ} {G : Y → ℂ}
    (hK : IsCompact (K : Set Γ)) (hKo : IsOpen (K : Set Γ)) (hA : IsOpen (A : Set Γ)) (hf : IsHecke A f)
    (hG : Lev fH G) : Lev fH (act (fH.comp ε) K f G) := by
  have hSm := sm_of_lev hε hG
  obtain ⟨U, hU, hUG⟩ := hG
  let L : Subgroup Γ := A ⊓ U.comap ε ⊓ K
  have hL : IsOpen (L : Set Γ) := (hA.inter (hU.preimage hε)).inter hKo
  obtain ⟨T, d, h⟩ := hint_lin hK hL (inf_le_right : L ≤ K) hf.1.isCompact
  have hsum : ∀ z, act (fH.comp ε) K f G z = d * ∑ q ∈ T, f q.out * G (z * fH (ε q.out)) := fun z =>
    h (fun m => f m * G (z * (fH.comp ε) m))
      (fun l hl x => term_inv hf z hl.1.1 (show (fH.comp ε) l ∈ rStab G from hUG _ hl.1.2) x)
      (fun x hx => term_supp x hx)
  let U' : Subgroup P := ⨅ q ∈ T, U.comap (MulAut.conj (ε (Quotient.out q))⁻¹).toMonoidHom
  refine ⟨U', ?_, fun u hu x => ?_⟩
  · have : (U' : Set P) = ⋂ q ∈ T, (fun y => (ε (Quotient.out q))⁻¹ * y * ((ε (Quotient.out q))⁻¹)⁻¹) ⁻¹' (U : Set P) := by
      ext y
      simp [U', Subgroup.mem_iInf, MulAut.conj_apply]
    rw [this]
    exact isOpen_biInter_finset fun q _ => hU.preimage (by fun_prop)
  · rw [hsum, hsum]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : (ε q.out)⁻¹ * u * ε q.out ∈ U := by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu q) hq)
      simpa [MulAut.conj_apply] using this
    have e1 : x * fH u * fH (ε q.out) = x * fH (ε q.out) * fH ((ε q.out)⁻¹ * u * ε q.out) := by
      simp only [map_mul, map_inv]
      group
    rw [e1, hUG _ hq']

end Act

end GlobalTheory.CompanionTheory.ActTr

end
