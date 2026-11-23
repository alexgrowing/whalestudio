import Mathlib
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop

noncomputable section

namespace GlobalTheory.CompanionTheory.BernNarrow

section
open GlobalTheory.PRep GlobalTheory.SmGL

def Narrow : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

end

section
open PositivityTheory.KCo GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_gen (hB : Narrow) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (hμ1 : μ ≠ 1) {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Γ × (GL (Fin n) k × GL (Fin t) k)) W) (hτ : IsSmooth (τ.comp (MonoidHom.inr Γ _)))
    (l : W →ₗ[ℂ] ℂ) (hs : Function.Surjective l)
    (hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ)
    (hk : ∀ x, l x = 0 → x ∈ twRel (τ.comp (MonoidHom.inl Γ _)) 1)
    (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp (τ.comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 := by
  let e := stdSum (rfl : n + t = n + t)
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ (Fin (n + t)) _ (two e)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two (Fin n) (Fin t))) _ :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let π₁ := detRep (Fin n) (1 : kˣ →* ℂˣ)
  let π₂ := detRep (Fin t) μ
  let ρD : Representation ℂ (Levi k (Two (Fin n) (Fin t))) (ℂ ⊗[ℂ] ℂ) :=
    (extTensor π₁ π₂).comp (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap ∘ₗ l
      isIntertwining' := fun m => LinearMap.ext fun φ => by
        change (TensorProduct.lid ℂ ℂ).symm (l (τ (1, m false, m true) φ)) =
          extTensor π₁ π₂ (m false, m true) ((TensorProduct.lid ℂ ℂ).symm (l φ))
        rw [hτl]
        simp [π₁, π₂, detRep] }
  have hq : Function.Surjective q := (TensorProduct.lid ℂ ℂ).symm.surjective.comp hs
  have hρ : IsSmooth ρ := isSmooth_comp hτ _ ((continuous_apply false).prodMk (continuous_apply true))
  have hI : (parInd (two e) ρD).IsIrreducible := hB k n t 1 μ (by unfold IsSmoothChar; simp) hμ (fun g => by simp) hu (Or.inr hμ1.symm)
  let σ := (twist ρ (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : Representation.IntertwiningMap σ ((twist ρD (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → Representation.IntertwiningMap σ σ := fun γ =>
    compMap (twistMap (actFst τ γ) (deltaHalf k (Two (Fin n) (Fin t)))) (leviProj k (two e))
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have h0 : l x = 0 := (TensorProduct.lid ℂ ℂ).symm.map_eq_zero_iff.1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y | ∃ γ z, y = T γ z - z})).2 ?_ (hk x h0)
    rintro _ ⟨γ, v, rfl⟩
    refine Submodule.subset_span ⟨γ, v, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    rfl
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL (Fin (n + t)) k) (parab k (two e)) (KO k _) hP
    GlobalTheory.SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k _) _ _ σ _ hσ α _ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  have hK : ∀ f, Φ f = 0 → f ∈ twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1 := fun f hf => by
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    refine Submodule.subset_span ⟨γ, z, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show τ (γ, 1) (z.1.1 x) = τ (γ, 1) (z.1.1 (x * 1))
    rw [mul_one]
  let S : Subrepresentation (parInd (two e) ρD) := ⟨N.map Φ.toLinearMap, by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨_, hN h f hf, ?_⟩
    rw [indSnd_inr]
    exact Φ.isIntertwining _ _ h f⟩
  rcases hI.eq_bot_or_eq_top S with h | h
  · refine Or.inr fun f hf => hK f ?_
    have : Φ.toLinearMap f ∈ S.toSubmodule := ⟨f, hf, rfl⟩
    rw [h] at this
    exact this
  · exact Or.inl (top_of_map Φ.toLinearMap hK hR (congrArg Subrepresentation.toSubmodule h))

theorem irr_ind (hB : Narrow) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (hμ1 : μ ≠ 1) (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp ((fibRep (Fin n) (Fin n) (Fin t) μ n).comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n) (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 := by
  let τ := fibRep (Fin n) (Fin n) (Fin t) μ n
  let ξ : GL (Fin n) k →* ℂˣ := detChar (Fin n) (μ⁻¹ * absPow k (((Fintype.card (Fin n) : ℂ) + Fintype.card (Fin t)) / 2))
  have hξ : IsSmoothChar ξ := (hμ.inv.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar
  obtain ⟨l, hs, hl, hk⟩ := exists_fun (k := k) (κ := n) (Fintype.card_fin n).symm hξ
  have hτ : IsSmooth (τ.comp (MonoidHom.inr _ _)) := GlobalTheory.T.fibre_representation_smooth k _ _ _ μ hμ n
  have hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ := by
    intro g p₁ p₂ φ
    change l ((fibChar (Fin n) (Fin n) (Fin t) μ (g, p₁, p₂) : ℂ) • fibBase (Fin n) (Fin n) n (g, p₁) φ) = _
    rw [map_smul, hl, smul_eq_mul, ← mul_assoc]
    congr 1
    have a1 : ∀ (x : kˣ) (s s' s'' : ℂ), s + s' + s'' = 0 → absPow k s x * absPow k s' x * absPow k s'' x = 1 := fun x s s' s'' h => by
      rw [← MonoidHom.mul_apply, ← absPow_add, ← MonoidHom.mul_apply, ← absPow_add, h]
      exact Units.ext (by simp [val_absPow])
    have b1 := congrArg Units.val (a1 (GeneralLinearGroup.det p₁) (-(n : ℂ) / 2) (-(t : ℂ) / 2) (((n : ℂ) + t) / 2) (by ring))
    have b2 := congrArg Units.val (a1 (GeneralLinearGroup.det p₂) (-(n : ℂ) / 2) ((n : ℂ) / 2) 0 (by ring))
    simp only [fibChar, ξ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply,
      Units.val_mul, MonoidHom.inv_apply, Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_one, val_absPow, Complex.cpow_zero,
      mul_one] at b1 b2 ⊢
    have n1 := (μ (GeneralLinearGroup.det g)).ne_zero
    have n2 := (μ (GeneralLinearGroup.det p₁)).ne_zero
    have n3 := (absPow k (((n : ℂ) + t) / 2) (GeneralLinearGroup.det g)).ne_zero
    rw [val_absPow] at n3
    simp only [neg_div] at b1 b2
    field_simp
    linear_combination (exp := 1) ((nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ (-((n : ℂ) / 2)) *
      (nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ ((n : ℂ) / 2)) * b1 + b2
  refine irr_gen hB n t hμ hu hμ1 τ hτ l hs hτl (fun x h0 => ?_) N hR hN
  refine (Submodule.span_le (p := twRel (τ.comp (MonoidHom.inl _ _)) 1)).2 ?_ (hk x h0)
  rintro _ ⟨γ, v, rfl⟩
  have e1 : τ (γ, 1) v = (ξ γ : ℂ) • rightRep (Fin n) (Fin n) n γ v := by
    change (fibChar (Fin n) (Fin n) (Fin t) μ (γ, 1) : ℂ) • fibBase (Fin n) (Fin n) n (γ, 1) v = _
    congr 1
    simp [fibChar, ξ]
  have h : rightRep (Fin n) (Fin n) n γ v - ((ξ⁻¹ γ : ℂˣ) : ℂ) • v =
      ((ξ⁻¹ γ : ℂˣ) : ℂ) • (τ (γ, 1) v - (((1 : GL (Fin n) k →* ℂˣ) γ : ℂˣ) : ℂ) • v) := by
    rw [e1, MonoidHom.one_apply, Units.val_one, one_smul, smul_sub, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)

end

section
open PositivityTheory.KCo GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem irrF' (hB : Narrow) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν) (hν1 : ν ≠ 1)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : augF n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y]) (inv_ne_one.2 hν1)) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end

section
open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip PositivityTheory.ThKG.LocalRamifiedLeviRestriction

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} {e : Fin d₁ ⊕ Bool ≃ Fin d} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem local_multiplicity_one_irreducible_GL (hB : Narrow) {L' : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W} (hL : Inv e ν L)
    (hL' : Inv e ν L') (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) (hn : n ≤ d₁)
    (ρ : GL (Fin d₁) k → Module.End ℂ W) (hr : Module.rank ℂ W ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ W, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hM : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L Φ))
    (hM' : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L' Φ))
    (h0 : ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' Φ = c • L Φ := by
  let S : Submodule ℂ (Matrix (Fin n) (Fin d₁) k → ℂ) :=
    { carrier := {ψ | Full ψ}, add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun Y h => by simp [ha.2 Y h, hb.2 Y h]⟩,
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩, smul_mem' := fun c a ha => ⟨(SB _).smul_mem c ha.1, fun Y h => by simp [ha.2 Y h]⟩ }
  let j := tn₁ e (one n) (one n : (Fin n → k) → ℂ)
  let A : GL (Fin d₁) k → S → S := fun g ψ => ⟨_, full_omB ψ.2 1 g⟩
  have jA : ∀ (g : GL (Fin d₁) k) (ψ : Matrix (Fin n) (Fin d₁) k → ℂ), j (fun Z : Matrix (Fin n) (Fin d₁) k => ψ ((1 : GL (Fin n) k).val * Z * g.val)) =
      fun Y : Matrix (Fin n) (Fin d) k => j ψ (Y * blk e g.val) := fun (g : GL (Fin d₁) k) ψ => funext fun Y => by
    have m1 : mid e (Y * blk e g.val) = mid e Y * g.val := by
      ext i s; simp only [mid, submatrix_apply, Matrix.mul_apply, id]; rw [sum_e (e := e)]; simp [blk]
    have m2 : ∀ t, cl e t (Y * blk e g.val) = cl e t Y := fun t => by
      ext i; simp only [cl, Matrix.mul_apply]; rw [sum_e (e := e)]; cases t <;> simp [blk]
    simp [j, tn₁, tn, m1, m2]
  let μ := L ∘ₗ j ∘ₗ S.subtype
  let μ' := L' ∘ₗ j ∘ₗ S.subtype
  have eA : ∀ g ψ, μ (A g ψ) = ρ g (μ ψ) := fun g ψ => (congrArg L (jA g ψ)).trans (hM g _ (tn_mem ψ.2.1 one_sb one_sb))
  have eA' : ∀ g ψ, μ' (A g ψ) = ρ g (μ' ψ) := fun g ψ => (congrArg L' (jA g ψ)).trans (hM' g _ (tn_mem ψ.2.1 one_sb one_sb))
  have ne : ¬ ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0 := fun h => let ⟨Φ, h1, h2⟩ := h0; h2 (red hL hu hl hν h Φ h1)
  have ker : ∀ ψ, μ ψ = 0 → μ' ψ = 0 := by
    rcases irrF' hB (α := 1) hn hu (fun h => hν (by simp [h])) (LinearMap.ker (L ∘ₗ j) ⊓ S) (le_inf (aug_ker hL hl hν) (Submodule.span_le.2 (by
      rintro _ ⟨g, ψ, h, rfl⟩
      refine sub_mem ?_ h
      have := S.smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) (full_omB h (invT g⁻¹) 1)
      convert this using 1
      funext Y
      simp [omB, invT]))) (fun g ψ h _ => by
        have e1 : omB ν 1 1 g ψ = apow (gdet g) ((n : ℂ) / 2) • (A g ⟨ψ, h.2⟩).1 := by
          funext Y
          simp [omB, A]
        rw [e1]
        refine Submodule.smul_mem _ _ ⟨?_, (A g ⟨ψ, h.2⟩).2⟩
        have : μ ⟨ψ, h.2⟩ = 0 := h.1
        exact (eA g ⟨ψ, h.2⟩).trans (by rw [this, map_zero])) with h | h
    · exact absurd (fun ψ hψ => (h ψ hψ).1) ne
    · exact fun ψ hψ => aug_ker hL' hl hν (h ψ.1 ⟨hψ, ψ.2⟩ ψ.2)
  have top : LinearMap.range μ = ⊤ := (hi _ (by rintro g _ ⟨ψ, rfl⟩; exact ⟨A g ψ, eA g ψ⟩)).resolve_left fun h =>
    ne fun ψ hψ => by
      have : μ ⟨ψ, hψ⟩ ∈ LinearMap.range μ := ⟨_, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  obtain ⟨s, hs⟩ := μ.exists_rightInverse_of_surjective top
  have th : ∀ ψ, (μ' ∘ₗ s) (μ ψ) = μ' ψ := fun ψ => by
    have := ker (s (μ ψ) - ψ) (by rw [map_sub, ← LinearMap.comp_apply μ s, hs, LinearMap.id_apply, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨c, hc⟩ := dixmier_commutant_scalar _ W ρ hr hi (μ' ∘ₗ s) fun g => LinearMap.ext fun x => by
    obtain ⟨ψ, rfl⟩ := LinearMap.range_eq_top.1 top x
    rw [Module.End.mul_apply, Module.End.mul_apply, ← eA, th, th, eA']
  refine ⟨c, fun Φ hΦ => sub_eq_zero.1 (red (L := L' - c • L) (e := e) ⟨fun g Ψ h => ?_, fun g hg Ψ h => ⟨(hL.right g hg Ψ h).1, ?_⟩⟩
    hu hl hν (fun ψ hψ => ?_) Φ hΦ)⟩
  · simp [hL.left g Ψ h, hL'.left g Ψ h]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, (hL.right g hg Ψ h).2, (hL'.right g hg Ψ h).2]
  · have := th ⟨ψ, hψ⟩
    rw [hc] at this
    exact sub_eq_zero.2 this.symm

end

section
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel PositivityTheory.ThKG.Loc PositivityTheory.ThKG.LocalRamifiedLeviRestriction
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem pair_multiplicity_one_ramified (hBe : Narrow) {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ r₃ s₃ : ℕ}
    (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂) (hW₁ : W₁.IsSkew σ B r₃ s₃) {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E}
    (hom : M.IsWeil B.ψ χX χW om) (hk : IsHecke F E χW) {K : Subgroup (AF F)ˣ} {m : ℕ} (res : ResEtaPow K χX m) {H : Plane E d d₁} {i₀ i₁}
    (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : E →ₐ[F] Fv F v) (ram : ¬ GlobalTheory.SplitWeil.IsUnram (chrW χW t)) (hn : n ≤ d₁)
    (hS : ∀ h₀ : GL (Fin d₁) (Fv F v), ∃ h ∈ UAt σ W₁ (evFin F v), (mat h).map (piW t) = h₀)
    {P : Type} [AddCommGroup P] [Module ℂ P] {τ : UA σ W₁.J → Module.End ℂ P} (τ1 : τ 1 = 1) (hr : Module.rank ℂ P ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ W₁ (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤) {r : ℝ} {Λ Λ' : Fl F v n d →ₗ[ℂ] P}
    (hΛ : Eqv om H χX r τ Λ) (hΛ' : Eqv om H χX r τ Λ') (h0 : ∃ φ ∈ SB _, Λ φ ≠ 0) : ∃ c : ℂ, ∀ φ ∈ SB _, Λ' φ = c • Λ φ := by
  obtain ⟨⟨sec, h⟩, hu⟩ := section_statement F E σ hB.cm v t
  obtain ⟨⟨ι₀, hι⟩, sX, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨kX, kW⟩ := k ι₀ hι
  let e : Fin d₁ ⊕ Bool ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hH.rank])
  have gr := fr_gram (e := e) hB.cm hH hW.skew
  have dC : ((fr H e).map t).det ≠ 0 := by
    have := congrArg det gr
    rw [det_mul, det_mul, det_transpose] at this
    have h1 : (fr H e).det ≠ 0 := fun h' => (gm_det (e := e) (Vac.skew_det hW₁)).ne_zero (by rw [← this, h', zero_mul, zero_mul])
    rw [show (fr H e).map t = (t : E →+* Fv F v).mapMatrix (fr H e) from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  let C : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero _ dC
  have hC : Fr σ t W W₁ H e C := ⟨rfl, gr, Vac.skew_det hW⟩
  let ι := chg 1 C⁻¹ 1 ι₀
  have bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) :=
    bij_smul (bij_comp hι.bij (lrH 1 C⁻¹)) one_ne_zero
  have rX : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1) := fun g₀ =>
    let ⟨g, hg, e1⟩ := sX g₀
    ⟨g, hg, reads_chg (kX g hg g₀ e1) fun Φ Y => B_left _ Φ Y (by simp) rfl⟩
  have rW : ∀ g ∈ UAt σ W (evFin F v), ∀ p : GL (Fin d) (Fv F v), (mat g).map (piW t) = (C * p * C⁻¹).val →
      Reads v ι (om (1, g)) (omB (chrW χW t) (chrW χX t) 1 p) := fun g hg p e1 =>
    reads_chg (kW g hg _ e1) fun Φ Y => B_right _ Φ Y (by rw [← Units.val_mul, ← Units.val_mul, mul_assoc C, inv_mul_cancel_left])
      (by simpa using gdet_conj C⁻¹ p)
  obtain ⟨s, hs⟩ := (ι ∘ₗ (SB _).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b hab =>
    Subtype.ext (bij.injOn a.2 b.2 hab))
  have s1 : ∀ φ ∈ SB _, (s (ι φ)).1 = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hs ⟨φ, hφ⟩)
  have rd : ∀ {T S}, Reads v ι T S → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), S Φ ∈ SB _ ∧
      Acts (evFin F v) T (s Φ).1 (s (S Φ)).1 := fun {T S} hR Φ hΦ => by
    obtain ⟨φ, hφ, rfl⟩ := bij.surjOn hΦ
    obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
    rw [← h3, s1 φ hφ, s1 φ₁ h1]
    exact ⟨bij.mapsTo h1, h2⟩
  have eo : ∀ (p : GL (Fin d) (Fv F v)) (Φ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ), omB (chrW χW t) (chrW χX t) 1 p Φ =
      ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) • fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val) := fun p Φ => by
    funext Y
    simp [omB]
  have c0 : ∀ p : GL (Fin d) (Fv F v), ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) ≠ 0 := fun p =>
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have inv : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → Inv e (chrW χW t) (Λ ∘ₗ (SB _).subtype ∘ₗ s) := fun {Λ} hΛ => by
    refine ⟨fun g₀ Φ hΦ => ?_, fun a ha Φ hΦ => ?_⟩
    · obtain ⟨g, hg, hR⟩ := rX g₀
      have e1 : omB (chrW χW t) 1 g₀ 1 Φ = omB (chrW χW t) (chrW χX t) g₀ 1 Φ := by
        funext Y
        simp [omB]
      have := hΛ.aug (Submodule.subset_span ⟨g, hg, _, (s Φ).2, _, (s _).2, (rd hR Φ hΦ).2, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [e1]
      exact this
    · have da := inP_det ha
      obtain ⟨p1, p2, p3, p4, p5⟩ := ha
      have x0 : a (e (.inr false)) (e (.inr false)) ≠ 0 := fun h => by simp [h] at p2
      have y0 : a (e (.inr true)) (e (.inr true)) ≠ 0 := fun h => by simp [h] at p3
      let x := Units.mk0 _ x0
      let y := Units.mk0 _ y0
      let p : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero a (da ▸ mul_ne_zero x0 y0)
      let pm : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero (bl e 1 x.val y.val) (by rw [usage₄]; simp)
      have im : (pm⁻¹).val = bl e 1 (x⁻¹).val (y⁻¹).val := by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        ext i j
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        rw [Matrix.mul_apply, sum_e' (e := e)]
        rcases i with i | _ | _ <;> rcases j with j | _ | _ <;> simp [pm, bl, Matrix.one_apply]
      have pu : ∀ i j, (p * pm⁻¹).val i (e j) = a i (e j) * Sum.elim (fun _ => 1) (fun b => cond b (y⁻¹).val (x⁻¹).val) j := fun i j => by
        rw [Units.val_mul, im, Matrix.mul_apply, sum_e' (e := e)]
        rcases j with j | _ | _ <;> simp [p, bl, Matrix.one_apply]
      obtain ⟨u, hu1, hu2⟩ := sW (C * (p * pm⁻¹) * C⁻¹)
      obtain ⟨m', hm1, hm2⟩ := sW (C * pm * C⁻¹)
      obtain ⟨z, z1, z2, z3, z4, z5⟩ := idele_two hB.cm t x y p2 p3
      have un := mem_unip h hC hu1 hu2 (fun i => by
        rw [pu]; split_ifs with hi
        · simp [hi, x, x0]
        · simp [p1 i hi]) (by rw [pu]; simp [y, y0]) (fun s s' => by rw [pu, p4, Matrix.one_apply]; simp) (fun s => by rw [pu, p5]; simp)
      have lv := is_levi h hC hm1 hm2 (one_UAt W₁) (x := x) (y := y) (by
        rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) z1 z2 z3
      have hR := rW (u * m') (mul_UAt hu1 hm1) p (by
        rw [show mat (u * m') = mat u * mat m' from rfl, Matrix.map_mul, hu2, hm2, ← Units.val_mul]; congr 1; group)
      obtain ⟨q1, q2⟩ := rd hR Φ hΦ
      have := hΛ.act z 1 m' lv (one_UAt W₁) u un hu1 hm1 _ (s Φ).2 _ (s _).2 q2
      have dp : gdet p = x * y := Units.ext da
      have ap : apow (x * y) ((n : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [x, y, p2, p3]) _
      rw [eo] at q1 this
      rw [map_smul, Submodule.coe_smul, map_smul, dp, ap, z4, z5 _ _ _ res, τ1] at this
      refine ⟨(Submodule.smul_mem_iff _ (c0 p)).1 q1, ?_⟩
      have h9 : Λ (s fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val)).1 = Λ (s Φ).1 := by simpa using this
      exact h9
  choose sc sc1 sc2 using hS
  have bd : ∀ g : GL (Fin d₁) (Fv F v), (bl e g.val 1 1).det ≠ 0 := fun g => by
    rw [usage₄, mul_one, mul_one]; exact g.det_ne_zero
  let pb : GL (Fin d₁) (Fv F v) → GL (Fin d) (Fv F v) := fun g => GeneralLinearGroup.mkOfDetNeZero _ (bd g)
  let ρ : GL (Fin d₁) (Fv F v) → Module.End ℂ P := fun g =>
    ((chrW χX t (gdet (pb g)) : ℂ) * apow (gdet (pb g)) ((n : ℂ) / 2))⁻¹ • τ (sc g)
  have lev : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      (Λ ∘ₗ (SB _).subtype ∘ₗ s) (fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * blk e g.val)) = ρ g ((Λ ∘ₗ (SB _).subtype ∘ₗ s) Φ) := fun {Λ} hΛ g Φ hΦ => by
    obtain ⟨m', hm1, hm2⟩ := sW (C * pb g * C⁻¹)
    have lv := is_levi h hC hm1 hm2 (sc1 g) (x := 1) (y := 1) (by rw [sc2]; rfl) (z := 1) (fun u _ => by simp) (by simp) (by simp)
    obtain ⟨-, q2⟩ := rd (rW m' hm1 _ hm2) Φ hΦ
    have := hΛ.act 1 _ m' lv (sc1 g) 1 (one_mem _) (one_UAt W) hm1 _ (s Φ).2 _ (s _).2 (by rw [one_mul]; exact q2)
    have bb : blk e g.val = (pb g).val := by
      change _ = bl e g.val 1 1
      rw [blk, bl]
      congr 2
      ext (_ | _) (_ | _) <;> simp
    rw [eo, map_smul, Submodule.coe_smul, map_smul] at this
    rw [bb]
    apply smul_right_injective _ (c0 (pb g))
    simp only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 (pb g)), one_smul]
    simpa using this
  obtain ⟨l, hl, hν⟩ : ∃ l : (Fv F v)ˣ, valuation (Fv F v) (l : Fv F v) = 1 ∧ chrW χW t l ≠ 1 := by
    by_contra h'
    exact ram fun x hx => by by_contra h''; exact h' ⟨x, hx, h''⟩
  obtain ⟨c, hc⟩ := local_multiplicity_one_irreducible_GL hBe (inv hΛ) (inv hΛ') (hu χW hk) hl hν hn ρ hr (fun N hN => hi N fun g hg x hx => by
    have e1 : sc (GeneralLinearGroup.map (piW t) g.1) = g := ua_ext h (Vac.skew_det hW₁) (sc1 _) hg (sc2 _)
    have := N.smul_mem ((chrW χX t (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) : ℂ) *
      apow (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) ((n : ℂ) / 2)) (hN (GeneralLinearGroup.map (piW t) g.1) x hx)
    simpa only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 _), one_smul, e1] using this) (lev hΛ) (lev hΛ') (by
      obtain ⟨φ, hφ, h0⟩ := h0
      exact ⟨ι φ, bij.mapsTo hφ, by simpa [s1 φ hφ] using h0⟩)
  exact ⟨c, fun φ hφ => by simpa [s1 φ hφ] using hc (ι φ) (bij.mapsTo hφ)⟩

theorem ramifiedMultiplicityOne_of_bernstein (hBe : Narrow) : RamifiedMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H i₀ i₁ χ r m m₁ st hH v hv lam lam' hl hl' h0
  have T := m.triple
  have T₁ := m₁.triple
  have hB := T.base
  let t := B.τ ⟨v, T.chars.sub hv⟩
  obtain ⟨sW₁, ex₁⟩ := acts_ex hB T₁.geo.hV T₁.geo.hW T₁.weil t
  obtain ⟨-, ex⟩ := acts_ex hB T.geo.hV T.geo.hW T.weil t
  obtain ⟨-, -, hν, -, ram, -⟩ := split_character_facts F E B X a a' v t T.chars
  have onto₁ : ∀ x, ∃ φ ∈ SB _, Rf₁.p v φ = x := fun x => Submodule.mem_map.1 ((m₁.fin.onto v).symm ▸ Submodule.mem_top)
  have onto : ∀ x, ∃ φ ∈ SB _, Rf.p v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto v).symm ▸ Submodule.mem_top)
  have onto' : ∀ x, ∃ φ ∈ SB _, Rf.p' v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto' v).symm ▸ Submodule.mem_top)
  have wd : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB _, ∀ ψ ∈ SB _, ∀ φ₁ ∈ SB _, ∀ ψ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
      Acts (evFin F v) (om₁ (1, h)) ψ ψ₁ → Rf₁.p v φ = Rf₁.p v ψ → Rf₁.p v φ₁ = Rf₁.p v ψ₁ := fun h hh φ a1 ψ a2 φ₁ a3 ψ₁ a4 b1 b2 e => by
    have := m₁.fin.equiv v h hh _ (add_mem a1 ((SB _).smul_mem (-1) a2)) 0 (zero_mem _) _ (add_mem a3 ((SB _).smul_mem (-1) a4)) 0
      (zero_mem _) (acts_lin (ex₁ h hh) a1 a2 b1 b2 (-1)) (PositivityTheory.ThKG.LocalRamifiedLeviRestriction.acts_zero _) (by simp [e])
    simpa [← sub_eq_add_neg, sub_eq_zero] using this
  have exτ : ∀ h : UA σ G₁.W.J, ∃ τ : Module.End ℂ (Rf₁.Pi v), h ∈ UAt σ G₁.W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om₁ (1, h)) φ φ₁ → τ (Rf₁.p v φ) = Rf₁.p v φ₁ := fun h => by
    by_cases hh : h ∈ UAt σ G₁.W (evFin F v)
    swap
    · exact ⟨0, fun h' => absurd h' hh⟩
    choose s s1 s2 using onto₁
    choose A A1 A2 using ex₁ h hh
    have k : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → Rf₁.p v (A _ (s1 (Rf₁.p v φ))) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => wd h hh _ (s1 _) _ b1 _ (A1 _ _) _ b2 (A2 _ _) b3 (s2 _)
    have lin : ∀ x y (c : ℂ), Rf₁.p v (A _ (s1 (x + c • y))) = Rf₁.p v (A _ (s1 x)) + c • Rf₁.p v (A _ (s1 y)) := fun x y c => by
      have := k _ (add_mem (s1 x) ((SB _).smul_mem c (s1 y))) _ (add_mem (A1 _ (s1 x)) ((SB _).smul_mem c (A1 _ (s1 y))))
        (acts_lin (ex₁ h hh) (s1 x) (s1 y) (A2 _ _) (A2 _ _) c)
      rw [map_add, map_smul, s2, s2, map_add, map_smul] at this
      exact this
    obtain ⟨f, hf⟩ : ∃ f : Rf₁.Pi v → Rf₁.Pi v, ∀ x, f x = Rf₁.p v (A _ (s1 x)) := ⟨_, fun _ => rfl⟩
    have k' : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → f (Rf₁.p v φ) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => (hf _).trans (k φ b1 φ₁ b2 b3)
    have lin' : ∀ x y (c : ℂ), f (x + c • y) = f x + c • f y := fun x y c => by rw [hf, hf, hf]; exact lin x y c
    have z : f 0 = 0 := by simpa using k' 0 (zero_mem _) 0 (zero_mem _) (PositivityTheory.ThKG.LocalRamifiedLeviRestriction.acts_zero _)
    exact ⟨{ toFun := f, map_add' := fun x y => by simpa using lin' x y 1,
             map_smul' := fun c y => by simpa [z] using lin' 0 y c }, fun _ => k'⟩
  choose τ hτ using exτ
  have τ1 : τ 1 = 1 := LinearMap.ext fun x => by
    obtain ⟨φ, h1, rfl⟩ := onto₁ x
    exact hτ 1 (one_UAt _) φ h1 φ h1 fun r _ => by rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]; rfl
  have hr : Module.rank ℂ (Rf₁.Pi v) ≤ Cardinal.aleph0 := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)
    refine le_trans ?_ (rank_SB (Fin a₁ × Fin (a₁ + a₁') → Fv F v))
    rw [← rank_top, ← m₁.fin.onto v]
    exact rank_map_le _ _
  have hi : ∀ N : Submodule ℂ (Rf₁.Pi v), (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    m₁.fin.irred v N fun h hh φ b1 φ₁ b2 b3 b4 => hτ h hh φ b1 φ₁ b2 b3 ▸ hN h hh _ b4
  have eq : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om H χ r τ (lam ∘ₗ Rf.p v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨φ₁, c1, c2⟩ := onto₁ (lam (Rf.p v φ))
        obtain ⟨φ₂, c3, c4⟩ := ex₁ h₁ hh φ₁ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hl z h₁ m' lv u hu b1 b2 φ b3 φ' b4 φ₁ c1 φ₂ c3 b5 c4 c2.symm, ← c2,
          hτ h₁ hh φ₁ c1 φ₂ c3 c4]⟩
  have eq' : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om' H χ r τ (lam ∘ₗ Rf.p' v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv' v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨ψ, c1, c2⟩ := onto (Rf.p' v φ)
        obtain ⟨ψ', c3, c4⟩ := ex _ (mul_UAt b1 b2) ψ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, ← m.fin.equiv v _ (mul_UAt b1 b2) ψ c1 φ b3 ψ' c3 φ' b4 c4 b5 c2, ← c2]
        exact (eq hl).act z h₁ m' lv hh u hu b1 b2 ψ c1 ψ' c3 c4⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h0 (LinearMap.ext h')
  rcases st with ⟨e1, e2, -, -, rfl, -⟩ | ⟨e1, e2, -, -, rfl, -⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV T.geo.hW T₁.geo.hW T.weil
      (show IsHecke F E (X.β / X.α) from ⟨T.chars.heckeβ.1.div' T.chars.heckeα.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resβ hH t
      (fun hu => ram hv fun y hy => by
        have := hu y hy
        rw [PositivityTheory.ThKG.LocalRamifiedLeviRestriction.chrW_div] at this
        rw [Chars.ν, PositivityTheory.ThKG.LocalRamifiedLeviRestriction.chrW_div, ← inv_div, this, inv_one]) (by omega) sW₁ τ1 hr hi (eq hl) (eq hl')
      (let ⟨φ, h1, h2⟩ := onto x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto y; h2 ▸ hc φ h1⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV' T.geo.hW T₁.geo.hW T.weil'
      (show IsHecke F E (X.α / X.β) from ⟨T.chars.heckeα.1.div' T.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resα hH t
      (ram hv) (by omega) sW₁ τ1 hr hi (eq' hl) (eq' hl')
      (let ⟨φ, h1, h2⟩ := onto' x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto' y; h2 ▸ hc φ h1⟩

end

open GlobalTheory.PRep GlobalTheory.SmGL in

theorem first_cohomology_ramified_narrow (NB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  ramifiedMultiplicityOne_of_bernstein NB

end GlobalTheory.CompanionTheory.BernNarrow
