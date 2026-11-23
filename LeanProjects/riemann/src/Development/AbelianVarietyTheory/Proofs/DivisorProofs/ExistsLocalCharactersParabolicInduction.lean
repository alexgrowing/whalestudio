import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterNormalizedEquivariantFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct

noncomputable section

open Matrix Filter Topology

namespace GlobalTheory.ThetaIsoGood

section Local

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mapA_add' {a a' : ℕ} {ν β : kˣ →* ℂˣ} {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l)
    {Φ Φ' : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) (h' : Φ' ∈ SB _) :
    mapA a' l ν β (Φ + Φ') = mapA a' l ν β Φ + mapA a' l ν β Φ' := by
  funext x
  rw [Pi.add_apply, mapA, mapA, mapA, ← hl.1 _ (restrict_X0 (omA_mem_SB ν β 1 x h)) _ (restrict_X0 (omA_mem_SB ν β 1 x h'))]
  congr 1
  funext g
  simp only [omA, Pi.add_apply, mul_add]

theorem mapA_smul' {a a' : ℕ} {ν β : kˣ →* ℂˣ} {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l) (c : ℂ)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (c • Φ) = c • mapA a' l ν β Φ := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mapA, mapA, ← hl.2.1 c _ (restrict_X0 (omA_mem_SB ν β 1 x h))]
  congr 1
  funext g
  simp only [omA, Pi.smul_apply, smul_eq_mul]
  ring

theorem mapA_left {a a' : ℕ} {ν β : kˣ →* ℂˣ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ}
    (hl : IsEqv ν (((a + a' : ℕ) : ℂ) / 2) l) (g : GL (Fin a) k)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (omA ν β g 1 Φ) = mapA a' l ν β Φ := by
  funext x
  have hs := restrict_X0 (omA_mem_SB ν β 1 x h)
  have e : omA ν β 1 x (omA ν β g 1 Φ) = omA ν β g 1 (omA ν β 1 x Φ) := by
    rw [← omA_mul, ← omA_mul, one_mul, mul_one, one_mul, mul_one]
  rw [mapA, mapA, e, ← hl.2.2 g⁻¹ 1 _ hs, ← hl.2.1 _ _ (comp_mul_mem_SB g⁻¹ 1 hs)]
  congr 1
  funext y
  simp only [omA, Pi.smul_apply, smul_eq_mul, map_one, map_inv, mul_one, Units.val_one, Matrix.mul_one, apow_one,
    Fintype.card_fin, apow_inv, Matrix.mul_assoc, neg_div, inv_one, Matrix.one_mul, one_mul]

theorem mapA_ne {a a' : ℕ} {ν β : kˣ →* ℂˣ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : ∃ φ ∈ SB _, l φ ≠ 0) :
    ∃ Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k), mapA a' l ν β Φ 1 ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := hl
  have hf := frame_rel (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  obtain ⟨Φ, hΦ, h⟩ := exists_extend_SB hf.1 hf.2.2.1 hf.2.2.2.2 hφ
  refine ⟨Φ, hΦ, ?_⟩
  have e : omA ν β 1 1 Φ = Φ := by funext X; simp [omA]
  rw [mapA, e, funext h]
  exact h0

theorem pairPlace_zero (b : Fin 2 → ℕ) (i : Fin (b 0)) :
    pairPlace b rfl ⟨0, i⟩ = finSumFinEquiv (Sum.inl i : Fin (b 0) ⊕ Fin (b 1)) := by
  ext; simp [pairPlace]

theorem pairPlace_one (b : Fin 2 → ℕ) (i : Fin (b 1)) :
    pairPlace b rfl ⟨1, i⟩ = finSumFinEquiv (Sum.inr i : Fin (b 0) ⊕ Fin (b 1)) := by
  ext; simp [pairPlace]

theorem pair_val (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (m : Levi k (fun j : Fin 2 => Fin (b j))) :
    (deltaHalf k _ m : ℂ) * (pairChar k b χ m : ℂ) =
      (χ 0 (gdet (m 0)) : ℂ) * χ 1 (gdet (m 1)) * apow (gdet (m 0)) ((b 1 : ℂ) / 2) * apow (gdet (m 1)) (-(b 0 : ℂ) / 2) := by
  have e0 : modExp (fun j : Fin 2 => Fin (b j)) 0 = b 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have e1 : modExp (fun j : Fin 2 => Fin (b j)) 1 = -(b 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  rw [deltaHalf_apply, pairChar, MonoidHom.finsetProd_apply, Fin.prod_univ_two, Fin.prod_univ_two, e0, e1]
  simp only [Units.val_mul, val_absPow, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply, apow,
    Int.cast_neg, Int.cast_natCast, gdet]
  ring

def indVal (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) :
    IndSp (pairPlace b rfl) (ofChar (pairChar k b χ)) →ₗ[ℂ] (GL (Fin (b 0 + b 1)) k → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem indVal_injective (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Function.Injective (indVal b χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem range_indVal (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) :
    LinearMap.range (indVal b χ) = indSp (b 0) (b 1) (χ 0) (χ 1) := by
  ext f
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨fun g A D N hg h => ?_, ?_⟩
    · have hp : g ∈ parab k (pairPlace b rfl) := by
        rw [mem_parab_iff]
        intro x y i j hlt
        fin_cases x <;> fin_cases y
        · exact absurd hlt (by decide)
        · exact absurd hlt (by decide)
        · exact (congrArg₂ g.val (pairPlace_one b i) (pairPlace_zero b j)).trans
            (congrFun (congrFun hg (Sum.inr i)) (Sum.inl j))
        · exact absurd hlt (by decide)
      have hA : leviProj k (pairPlace b rfl) ⟨g, hp⟩ 0 = A := by
        ext i j
        exact (congrArg₂ g.val (pairPlace_zero b i) (pairPlace_zero b j)).trans
            (congrFun (congrFun hg (Sum.inl i)) (Sum.inl j))
      have hD : leviProj k (pairPlace b rfl) ⟨g, hp⟩ 1 = D := by
        ext i j
        exact (congrArg₂ g.val (pairPlace_one b i) (pairPlace_one b j)).trans
            (congrFun (congrFun hg (Sum.inr i)) (Sum.inr j))
      have := parInd_law _ _ F ⟨g, hp⟩ h
      rw [ofChar_apply, smul_eq_mul, ← mul_assoc, pair_val, hA, hD] at this
      exact this
    · have ho := isSmooth_parInd (pairPlace b rfl) (ofChar (pairChar k b χ)) F
      exact Filter.mem_of_superset (IsOpen.mem_nhds ho (by simp)) fun u hu h =>
        congrFun (congrArg (fun G => G.1.1) (show parInd _ _ u F = F from hu)) h
  · rintro ⟨h1, h2⟩
    refine ⟨⟨⟨f, fun p g => ?_⟩, mem_smoothPart_of_nhds (h2.mono fun u hu => Subtype.ext (funext hu))⟩, rfl⟩
    show f (p * g) = (deltaHalf k _ (leviProj k _ p) : ℂ) • ofChar (pairChar k b χ) (leviProj k _ p) (f g)
    rw [ofChar_apply, smul_eq_mul, ← mul_assoc, pair_val]
    refine h1 p _ _ (fun i j => p.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) ?_ g
    ext (i | i) (j | j)
    · exact (congrArg₂ p.1.val (pairPlace_zero b i) (pairPlace_zero b j)).symm
    · rfl
    · exact (congrArg₂ p.1.val (pairPlace_one b i) (pairPlace_zero b j)).symm.trans
        (mem_parab_iff.1 p.2 1 0 i j (by decide))
    · exact (congrArg₂ p.1.val (pairPlace_one b i) (pairPlace_one b j)).symm

theorem indVal_pairInd (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (h : GL (Fin (b 0 + b 1)) k)
    (f : IndSp (pairPlace b rfl) (ofChar (pairChar k b χ))) :
    indVal b χ (pairInd k b rfl χ h f) = fun y => indVal b χ f (y * h) := rfl

theorem exists_lift {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ U) (j : V →ₗ[ℂ] W) (hj : Function.Injective j) (f : U → W) (hI : ∀ x ∈ S, f x ∈ LinearMap.range j)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y) (hsm : ∀ c : ℂ, ∀ x ∈ S, f (c • x) = c • f x) :
    ∃ p : U →ₗ[ℂ] V, ∀ x ∈ S, j (p x) = f x := by
  let q : S →ₗ[ℂ] LinearMap.range j :=
    { toFun := fun x => ⟨f x, hI x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd x x.2 y y.2)
      map_smul' := fun c x => Subtype.ext (hsm c x x.2) }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend ((LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ q)
  refine ⟨p, fun x hx => ?_⟩
  have e : p x = (LinearEquiv.ofInjective j hj).symm (q ⟨x, hx⟩) := LinearMap.congr_fun hp ⟨x, hx⟩
  rw [e, LinearEquiv.ofInjective_symm_apply]
  rfl

theorem map_eq_top_of_irr {U V H : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [Group H]
    (S : Submodule ℂ U) (j : V →ₗ[ℂ] (H → ℂ)) (hj : Function.Injective j) (I : Submodule ℂ (H → ℂ))
    (hr : LinearMap.range j = I)
    (hI : ∀ N : Submodule ℂ (H → ℂ), N ≤ I → (∀ f ∈ N, ∀ x, (fun h => f (h * x)) ∈ N) → N = ⊥ ∨ N = I)
    (p : U →ₗ[ℂ] V) (heq : ∀ φ ∈ S, ∀ x, ∃ φ₁ ∈ S, j (p φ₁) = fun h => j (p φ) (h * x))
    (hne : ∃ φ ∈ S, p φ ≠ 0) : S.map p = ⊤ := by
  subst hr
  rcases hI ((S.map p).map j) LinearMap.map_le_range (by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩ x
    obtain ⟨φ₁, h1, h2⟩ := heq φ hφ x
    exact ⟨_, ⟨φ₁, h1, rfl⟩, h2⟩) with h | h
  · obtain ⟨φ, hφ, h0⟩ := hne
    have : j (p φ) ∈ (S.map p).map j := ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (hj (this.trans (map_zero j).symm)) h0
  · exact Submodule.map_injective_of_injective hj (h.trans (Submodule.map_top j).symm)

theorem exists_zeta (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (h0 : IsSmU (χ 0)) (h1 : IsSmU (χ 1)) (hν : IsSmU (χ 0 / χ 1)) (hu : IsUnram (χ 0 / χ 1)) :
    ∃ P : (Matrix (Fin (b 0)) (Fin (b 0 + b 1)) k → ℂ) →ₗ[ℂ] IndSp (pairPlace b rfl) (ofChar (pairChar k b χ)),
      (∀ y, ∃ Φ ∈ SB _, P Φ = y) ∧ (∃ Φ ∈ SB _, P Φ ≠ 0) ∧
      (∀ g, ∀ Φ ∈ SB _, P (omA (χ 0 / χ 1) (χ 1) g 1 Φ) = P Φ) ∧
      ∀ h, ∀ Φ ∈ SB _, P (omA (χ 0 / χ 1) (χ 1) 1 h Φ) = pairInd k b rfl χ h (P Φ) := by
  obtain ⟨l, hl, hl1⟩ := GlobalTheory.T.unramified_character_normalized_equivariant_functional k (b 0) _ (((b 0 + b 1 : ℕ) : ℂ) / 2) hν hu
  obtain ⟨P, hp⟩ := exists_lift (SB (Matrix (Fin (b 0)) (Fin (b 0 + b 1)) k)) (indVal b χ) (indVal_injective b χ)
    (mapA (b 1) l (χ 0 / χ 1) (χ 1)) (fun Φ hΦ => by
      rw [range_indVal]
      exact GlobalTheory.KSplitInd.mapA_mem_indSp k _ _ _ _ l h1 hl Φ hΦ)
    (fun x hx y hy => mapA_add' hl hx hy) (fun c x hx => mapA_smul' hl c hx)
  have tr0 : ∀ h, ∀ Φ ∈ SB _, indVal b χ (P (omA (χ 0 / χ 1) (χ 1) 1 h Φ)) = fun y => indVal b χ (P Φ) (y * h) :=
    fun h Φ hΦ => by
    funext y
    rw [hp _ (omA_mem_SB _ _ _ _ hΦ), mapA_omA_right, hp _ hΦ]
  have ne : ∃ Φ ∈ SB _, P Φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h0⟩ := mapA_ne (a' := b 1) (ν := χ 0 / χ 1) (β := χ 1) (l := l)
      ⟨_, indicator_intM_mem_SB, by rw [hl1]; exact one_ne_zero⟩
    exact ⟨Φ, hΦ, fun h => h0 (by rw [← hp Φ hΦ, h, map_zero, Pi.zero_apply])⟩
  have on := map_eq_top_of_irr _ _ (indVal_injective b χ) _ (range_indVal b χ)
    (indSp_irreducible H k (b 0) (b 1) _ _ h0 h1) P
    (fun Φ hΦ x => ⟨_, omA_mem_SB (χ 0 / χ 1) (χ 1) 1 x hΦ, tr0 x Φ hΦ⟩) ne
  refine ⟨P, fun y => ?_, ne, fun g Φ hΦ => indVal_injective b χ ?_,
    fun h Φ hΦ => indVal_injective b χ ((tr0 h Φ hΦ).trans (indVal_pairInd b χ h _).symm)⟩
  · exact Submodule.mem_map.1 (on.ge Submodule.mem_top)
  · rw [hp _ (omA_mem_SB _ _ _ _ hΦ), hp _ hΦ, mapA_left hl g hΦ]

theorem exists_zeta' (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (a a' : ℕ) (α β : kˣ →* ℂˣ)
    (h0 : IsSmU α) (h1 : IsSmU β) (hν : IsSmU (α / β)) (hu : IsUnram (α / β)) :
    ∃ P : (Matrix (Fin a) (Fin (a + a')) k → ℂ) →ₗ[ℂ]
        IndSp (pairPlace (N := a + a') ![a, a'] rfl) (ofChar (pairChar k ![a, a'] ![α, β])),
      (∀ y, ∃ Φ ∈ SB _, P Φ = y) ∧ (∃ Φ ∈ SB _, P Φ ≠ 0) ∧
      (∀ g, ∀ Φ ∈ SB _, P (omA (α / β) β g 1 Φ) = P Φ) ∧
      ∀ h, ∀ Φ ∈ SB _, P (omA (α / β) β 1 h Φ) = pairInd k (N := a + a') ![a, a'] rfl ![α, β] h (P Φ) :=
  exists_zeta H ![a, a'] ![α, β] h0 h1 hν hu

end Local

section Adelic

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
  GlobalTheory.KFinLoc GlobalTheory.SmGL GlobalTheory.LeviBlockExponent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_of_triple (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) := by
  refine ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, ⟨?_, fun x => ?_⟩, h.chars.resβ, fun u => ?_, h.weil⟩
  · show Continuous fun x => X.β x / X.α x
    exact h.chars.heckeβ.1.div' h.chars.heckeα.1
  · rw [MonoidHom.div_apply, h.chars.heckeβ.2 x, h.chars.heckeα.2 x, div_one]
  · rw [MonoidHom.div_apply, Circle.coe_div, h.chars.resβ u, h.chars.resα u]
    split_ifs
    · simp
    · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

omit [NumberField E] in

theorem one_mem_at {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

end Adelic

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct

set_option maxHeartbeats 1600000 in

theorem exists_map_onto_pairInd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsSmoothChar (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ Z : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)),
        (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁)).map Z = ⊤ ∧
        (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), Z φ = 0 → φ ∈ augAt om B.v₁) ∧
        ∀ (g : GL (Fin (a + a')) (Fv F B.v₁)) (h : UA σ G.W.J), h ∈ UAt σ G.W (evFin F B.v₁) →
          (mat h).map (piW B.τ₁) = g.1 →
          ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁),
            Acts (evFin F B.v₁) (om (1, h)) φ φ₁ → Z φ₁ = pairInd (Fv F B.v₁) b hb χ g (Z φ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hK hT
  have hP := hK.base
  have hv := hT.chars.good
  obtain ⟨hα, -, hrα⟩ := GlobalTheory.ChrWLocal.chrW_local F E X.α hT.chars.heckeα B.v₁ B.τ₁
  obtain ⟨hβ, -, hrβ⟩ := GlobalTheory.ChrWLocal.chrW_local F E X.β hT.chars.heckeβ B.v₁ B.τ₁
  have hw : splitPrime B.τ₁ ∉ GlobalTheory.LFun.above E (X.T : Set (Pl F)) := by
    show ¬ (splitPrime B.τ₁).under (𝓞 F) ∈ (X.T : Set (Pl F))
    rw [splitPrime_under]
    exact hv.1
  have uα := hrα.2 (hT.chars.unrα _ hw)
  have uβ := hrβ.2 (hT.chars.unrβ _ hw)
  have hdiv : chrW (X.β / X.α) B.τ₁ = chrW X.β B.τ₁ / chrW X.α B.τ₁ := by
    ext x
    simp [chrW, GlobalTheory.LFun.locChar]
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_of_triple hT) B.v₁ B.τ₁ 1 1
  have act := fun g hg h hh φ hφ φ₁ hφ₁ H => GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_of_triple hT)
    B.v₁ B.τ₁ 1 1 ι hι g hg h hh φ hφ φ₁ hφ₁ H
  rw [hdiv, inv_div] at act
  set α := chrW X.α B.τ₁
  set β := chrW X.β B.τ₁
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have m : ∀ φ ∈ GlobalTheory.WeilM.SB _, ι φ ∈ GlobalTheory.SplitWeil.SB _ := fun φ h => hb.mapsTo h
  have hν : GlobalTheory.KSplit.IsSmU (α / β) := by
    refine ⟨Subgroup.isOpen_mono (H₁ := α.ker ⊓ β.ker) (fun x hx => ?_) (hα.1.inter hβ.1), fun x => ?_⟩
    · rw [MonoidHom.mem_ker, MonoidHom.div_apply, hx.1, hx.2, div_one]
    · rw [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, hα.2, hβ.2, div_one]
  have uν : IsUnram (α / β) := fun x hx => by rw [MonoidHom.div_apply, uα x hx, uβ x hx, div_one]
  obtain ⟨P, hon, hne, hl, hr⟩ := exists_zeta' hP.bernsteinUnitaryProductIrreducible a a' α β hα hβ hν uν
  obtain ⟨Z, hZ⟩ : ∃ Z : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ]
      IndSp (pairPlace (N := a + a') ![a, a'] rfl) (ofChar (pairChar (Fv F B.v₁) ![a, a'] ![α, β])),
      ∀ φ, Z φ = P (ι φ) := ⟨P ∘ₗ ι, fun _ => rfl⟩
  have tr : ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _,
      Acts (evFin F B.v₁) (om (1, h)) φ φ₁ →
      Z φ₁ = pairInd (Fv F B.v₁) (N := a + a') ![a, a'] rfl ![α, β] (GlobalTheory.KSplit.locMat B.τ₁ 1 h) (Z φ) :=
    fun h hh φ hφ φ₁ hφ₁ H => by
    have e := act 1 (one_mem_at _ _) h hh φ hφ φ₁ hφ₁ H
    rw [map_one] at e
    exact (hZ φ₁).trans ((congrArg P e).trans ((hr _ _ (m φ hφ)).trans (congrArg _ (hZ φ).symm)))
  have tl : ∀ g ∈ UAt σ G.V (evFin F B.v₁), ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _,
      Acts (evFin F B.v₁) (om (g, 1)) φ φ₁ → Z φ₁ = Z φ := fun g hg φ hφ φ₁ hφ₁ H => by
    have e := act g hg 1 (one_mem_at _ _) φ hφ φ₁ hφ₁ H
    rw [map_one] at e
    exact (hZ φ₁).trans ((congrArg P e).trans ((hl _ _ (m φ hφ)).trans (hZ φ).symm))
  have on : (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁)).map Z = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨Φ, hΦ, e⟩ := hon y
    obtain ⟨φ, hφ, e'⟩ := hb.surjOn hΦ
    exact Submodule.mem_map.2 ⟨φ, hφ, (hZ φ).trans ((congrArg P e').trans e)⟩
  have ker : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), Z φ = 0 → φ ∈ augAt om B.v₁ := by
    rcases GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' hT B.v₁ hv
      (GlobalTheory.NuGood.not_root_of_unity F E σ B a a' G X om om' hT B.v₁ hv) (GlobalTheory.WeilM.SB _ ⊓ LinearMap.ker Z)
      (Submodule.span_le.2 (by
        rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, H, rfl⟩
        exact ⟨sub_mem hφ₁ hφ, LinearMap.sub_mem_ker_iff.2 (tl g hg φ hφ φ₁ hφ₁ H)⟩)) inf_le_left
      (fun h hh φ hφ φ₁ hφ₁ H => ⟨hφ₁, LinearMap.mem_ker.2 ((tr h hh φ hφ.1 φ₁ hφ₁ H).trans
        ((congrArg _ (LinearMap.mem_ker.1 hφ.2)).trans (map_zero _)))⟩) with h | h
    · exact fun φ hφ h0 => h.le ⟨hφ, LinearMap.mem_ker.2 h0⟩
    · obtain ⟨Φ, hΦ, h0⟩ := hne
      obtain ⟨φ, hφ, e'⟩ := hb.surjOn hΦ
      exact absurd ((congrArg P e').symm.trans ((hZ φ).symm.trans (LinearMap.mem_ker.1 (h.ge hφ).2))) h0
  refine ⟨![a, a'], rfl, ![α, β], Or.inl ⟨rfl, rfl⟩, Fin.forall_fin_two.2 ⟨hα.1, hβ.1⟩,
    Fin.forall_fin_two.2 ⟨hα.2, hβ.2⟩, Z, on, ker, fun g h hh hg φ hφ φ₁ hφ₁ H => ?_⟩
  have e : GlobalTheory.KSplit.locMat B.τ₁ 1 h = g := by
    refine Units.ext ?_
    rw [GlobalTheory.KSplit.locMat_val, hg]
    simp
  subst e
  exact tr h hh φ hφ φ₁ hφ₁ H

end GlobalTheory.ThetaIsoGood

end
