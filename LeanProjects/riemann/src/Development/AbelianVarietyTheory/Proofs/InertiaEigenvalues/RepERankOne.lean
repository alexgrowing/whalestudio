import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst

namespace GlobalTheory.TwistAbove

def twGL {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K) :
    Γ →* GL (Fin a) K where
  toFun g := ⟨((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    (((χ g)⁻¹ : Kˣ) : K) • (((r g)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by rw [smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [smul_mul_smul_comm, Units.inv_mul, Units.inv_mul, one_smul]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    change ((χ (g * h) : Kˣ) : K) • ((r (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *
      (((χ h : Kˣ) : K) • ((r h : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))
    rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul, Units.val_mul])

@[simp] theorem twGL_val {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (g : Γ) : ((twGL χ r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      ((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

abbrev chr {L : FinExt l} (m : ↥Gw →* GL (Fin 1) ↥L.1) : ↥Gw →* (↥L.1)ˣ :=
  Matrix.GeneralLinearGroup.det.comp m

theorem isModel_twGL {L : FinExt l} {r r' : ↥Gw →* GL (Fin a) (Om l)} {μ : ↥Gw →* (Om l)ˣ}
    (hr' : ∀ g, ((r' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ((μ g : (Om l)ˣ) : Om l) • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw (rk1 μ) L m) :
    IsModel Bw r' L (twGL (chr m) r₁) := by
  refine ⟨h₁.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) h₁.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) h₂.2
  simp only [mapRep, rk1] at e1 e2 ⊢
  simp at e1 e2 ⊢
  rw [hr']
  simp [← e1, ← e2]

section Common

variable {L : FinExt l} (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (m : ↥Gw →* GL (Fin 1) ↥L.1)

theorem repE_twGL (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (twGL (chr m) r₁) g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L r₁ g x := by
  change Matrix.toLin' ((twGL (chr m) r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem repE_rank_one (g : ↥(GK Bw.Kw)) (x : Fin 1 → ↥L.1) :
    Bw.repE L m g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • x := by
  funext i
  fin_cases i
  simp [LocBridge.repE, Matrix.mulVec, dotProduct, Matrix.det_unique]

theorem isDR_iff (P : LocPrime l) {n : ℕ} (s : ↥Gw →* GL (Fin n) ↥L.1) :
    IsDR (P.PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE P L s := by
  rw [IsDR, LocBridge.IsdRE, Module.finrank_fin_fun]

theorem twist_common {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    (Bw.IsdRE P L r₁ → Bw.IsdRE P L m → Bw.IsdRE P L (twGL (chr m) r₁)) ∧
    (Bw.IsCrysE P L r₁ → Bw.IsCrysE P L m → Bw.IsCrysE P L (twGL (chr m) r₁)) ∧
    (Bw.IsPotCrysE P L r₁ → Bw.IsPotCrysE P L m → Bw.IsPotCrysE P L (twGL (chr m) r₁)) ∧
    ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (b : ℤ), Bw.IsdRE P L m →
      (∀ n, Bw.multE P L m τ' n = if n = b then 1 else 0) →
      ∀ n, Bw.multE P L (twGL (chr m) r₁) τ' (n + b) = Bw.multE P L r₁ τ' n := by
  have hν := repE_rank_one Bw m
  have hρ := repE_twGL Bw r₁ m
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [← isDR_iff] at h1 h2 ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ h2).1 h1
  · exact (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T Bw.Kw L (Fin a → ↥L.1)
      _ _ _ _ hν hρ h2).1 h1
  · rintro ⟨K₁, k₁, c₁⟩ ⟨K₂, k₂, c₂⟩
    have l₁ : K₁.1 ≤ (supExt K₁ K₂).1 := le_sup_left
    have l₂ : K₂.1 ≤ (supExt K₁ K₂).1 := le_sup_right
    have k₃ : Bw.Kw.1 ≤ (supExt K₁ K₂).1 := k₁.trans l₁
    have d₁ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₁ _ T c₁
    have d₂ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₂ _ T c₂
    have e₁ : ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₁))).comp (Subgroup.inclusion (GK_le l₁)) =
        (Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    have e₂ : ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₂))).comp (Subgroup.inclusion (GK_le l₂)) =
        (Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    rw [e₁] at d₁
    rw [e₂] at d₂
    exact ⟨supExt K₁ K₂, k₃, (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T
      (supExt K₁ K₂) L (Fin a → ↥L.1) ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃))) _
      ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃))) _ (fun g x => hν _ x) (fun g x => hρ _ x) d₂).1 d₁⟩
  · intro τ' b hm hmult n
    exact GlobalTheory.TwistJump.multV_twist_char l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ
      ((isDR_iff Bw P m).2 hm) τ' b hmult n

end Common

theorem twist_above : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ), ∀ (r r' : ↥Gw →* GL (Fin a) (Loc.Om l)) (μ : ↥Gw →* (Loc.Om l)ˣ), (∀ g, ((r' g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) = ((μ g : (Loc.Om l)ˣ) : Loc.Om l) • ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → (IsdRAt P Bw r → IsdRAt P Bw (rk1 μ) → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 μ) → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw (rk1 μ) → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Loc.Om l) (J : Multiset ℤ) (c : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 μ) τ {c} → IsJumpsAt P Bw r' τ (J.map (· + c)) := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r r' μ hr'
  obtain ⟨T⟩ := hT
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun τ J c h1 h2 => ?_⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.1 ((local_ext P Bw l₁ r₁).1.2 d₁) ((local_ext P Bw l₂ r₂).1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.2.1 ((local_ext P Bw l₁ r₁).2.2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁, τ₁, i₁, c₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂, τ₂, i₂, c₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have j₁ : IsInduced Bw τ ((IntermediateField.inclusion l₁).comp τ₁) := fun x => i₁ x
    have j₂ : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ₂) := fun x => i₂ x
    have eτ := IsInduced.unique j₁ j₂
    have hd₂ := (local_ext P Bw l₂ r₂).2.1.2 d₂
    have hc := twist_common Bw (mapRep (IntermediateField.inclusion l₁).toRingHom r₁)
      (mapRep (IntermediateField.inclusion l₂).toRingHom r₂) T
    have hm : ∀ n, Bw.multE P (supExt L₁ L₂) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
        ((IntermediateField.inclusion l₁).comp τ₁) n = if n = c then 1 else 0 := by
      intro n
      rw [eτ, (local_ext P Bw l₂ r₂).2.2.2 τ₂ n, ← c₂ n, Multiset.count_singleton]
      split_ifs <;> simp
    refine ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      hc.1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) hd₂, _, j₁, fun n => ?_⟩
    have e1 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) J (add_left_injective c) (n - c)
    simp only [sub_add_cancel] at e1
    have e2 := hc.2.2.2 _ c hd₂ hm (n - c)
    rw [sub_add_cancel] at e2
    rw [e1, e2, (local_ext P Bw l₁ r₁).2.2.2 τ₁ (n - c), c₁]

end GlobalTheory.TwistAbove
