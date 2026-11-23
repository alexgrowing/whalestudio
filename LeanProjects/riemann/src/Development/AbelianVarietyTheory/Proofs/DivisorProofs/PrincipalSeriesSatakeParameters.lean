import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def toFun {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) :
    IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus (w.adicCompletion E) (Fin n)).symm.toMonoidHom)
      →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_injective {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) : Function.Injective (toFun w χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toFun_intertwines {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (g) (f) :
    toFun w χ (prinSeries χ g f) = rightReg ℂ _ ℂ g (toFun w χ f) := rfl

theorem hasSatGL_prinSeries {n : ℕ} (α : Fin n → ℂˣ) :
    HasSatGL w (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (Finset.univ.val.map α) := by
  have hK : KO (w.adicCompletion E) (Fin n) = KGL w n := SphCompletion.KO_completion w n
  constructor
  · obtain ⟨φ, h, h1, -⟩ := Formalism.UG.Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    obtain ⟨f, hf, rfl⟩ := (SphCompletion.isSpherical_iff E w n α _).1 h
    refine (Submodule.ne_bot_iff _).2 ⟨f, hK ▸ hf, fun h0 => ?_⟩
    subst h0
    simp at h1
  · intro x hx h0
    have hx' : x ∈ fixed (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (KO (w.adicCompletion E) (Fin n)) :=
      hK ▸ hx
    have hs := (SphCompletion.isSpherical_iff E w n α x.1.1).2 ⟨x, hx', rfl⟩
    exact IsSatVecGL.of_map (toFun w _) (toFun_intertwines w _) (toFun_injective w _)
      (isSatVecGL_of_isSpherical hs fun h => h0 (toFun_injective w _ (h.trans (map_zero _).symm)))

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_parab_one (g : GL (Fin 1) k) : g ∈ parab k (points (Fin 1)) :=
  mem_parab_iff.2 fun a b _ _ hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

theorem cB_one (μ : kˣ →* ℂˣ) (p : parab k (points (Fin 1))) :
    PrinProd.cB (fun _ : Fin 1 => μ) p = μ (Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k)) := by
  rw [PrinProd.cB_eq, Fin.prod_univ_one, Fin.prod_univ_one]
  have h : PrinProd.dg p 0 = Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    ext
    rw [PrinProd.val_dg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  rw [h]
  simp

def oneEquiv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    (detRep (Fin 1) μ).Equiv (prinSeries fun _ : Fin 1 => μ) := by
  let Ψ : ℂ →ₗ[ℂ] IndSp (points (Fin 1))
      ((ofChar (torusChar fun _ : Fin 1 => μ)).comp (leviTorus k (Fin 1)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun g => (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * c, fun p g => by
          show _ = PrinProd.sB (fun _ : Fin 1 => μ) p _
          rw [PrinProd.sB_apply, cB_one]
          beta_reduce
          rw [map_mul, map_mul, Units.val_mul, mul_assoc]⟩,
        MultiIrr.mem_smooth_of_eventually _ (Filter.mem_of_superset
          (IsOpen.mem_nhds (hμ.detChar (n := Fin 1)) (one_mem _)) fun u hu x => by
            have hu' : detChar (Fin 1) μ u = 1 := hu
            show (μ (Matrix.GeneralLinearGroup.det (x * u)) : ℂ) * c = (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * c
            rw [map_mul (Matrix.GeneralLinearGroup.det), map_mul, ← detChar_apply (n := Fin 1) μ u, hu', mul_one])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_add _ _ _))
      map_smul' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_left_comm _ _ _)) }
  refine Representation.Equiv.mk' ⟨Ψ, fun g => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    (fun F => F.1.1 1) (fun c => ?_) (fun F => Subtype.ext (Subtype.ext (funext fun g => ?_)))
  · show (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * (detRep (Fin 1) μ g c) =
      (μ (Matrix.GeneralLinearGroup.det (x * g)) : ℂ) * c
    simp [detRep, ofChar_apply, mul_assoc]
  · show (μ (Matrix.GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂ) * c = c
    simp
  · show (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1.1 1 = F.1.1 g
    have h := parInd_law (points (Fin 1)) _ F ⟨g, mem_parab_one g⟩ 1
    rw [mul_one] at h
    rw [h]
    change _ = PrinProd.sB (fun _ : Fin 1 => μ) ⟨g, mem_parab_one g⟩ _
    rw [PrinProd.sB_apply, cB_one]

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

theorem hasSatGL_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv σ) {B : Multiset ℂˣ} (h : HasSatGL w σ B) : HasSatGL w ρ B := by
  let f : V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap
  have hi : ∀ g y, f (ρ g y) = σ g (f y) := fun g y => e.toIntertwiningMap.isIntertwining _ _ g y
  have inj : Function.Injective f := e.toLinearEquiv.injective
  constructor
  · obtain ⟨y, hy⟩ := h.exists_vec
    have hfy : f (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    have hs : IsSatVecGL w ρ (e.toLinearEquiv.symm y) B := IsSatVecGL.of_map f hi inj (by rw [hfy]; exact hy)
    exact (Submodule.ne_bot_iff _).2 ⟨_, hs.2.1, hs.1⟩
  · intro x hx h0
    have hfx : f x ∈ fixed σ (KGL w n) :=
      GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hi, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
    exact IsSatVecGL.of_map f hi inj (h.2 _ hfx fun h1 => h0 (inj (h1.trans (map_zero f).symm)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_unrChar_of_ord {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : ord k ϖ = 1) :
    χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hϖ, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

theorem ord_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ord (w.adicCompletion E) (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) = 1 := by
  have h : Valued.v ((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [SphCompletion.ord_completion, h, WithZero.log_exp, neg_neg]

theorem univ_map_two (a b : ℂˣ) : (Finset.univ.val.map ![a, b] : Multiset ℂˣ) = {a, b} := by
  simp [Fin.univ_val_map, List.ofFn_succ]
  rfl

end GlobalTheory.PrinSat

theorem GlobalTheory.PrinSat.hasSatGL_prod₂_detRep : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (μ₁ μ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ →
    GlobalTheory.LFun.HasSatGL w (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂))
      {μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)), μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))} := by
  intro E _ _ w μ₁ μ₂ h1 h2
  have e1 := GlobalTheory.PrinSat.eq_unrChar_of_ord h1 (GlobalTheory.PrinSat.ord_unif w)
  have e2 := GlobalTheory.PrinSat.eq_unrChar_of_ord h2 (GlobalTheory.PrinSat.ord_unif w)
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂)
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂)
  let T := (GlobalTheory.LocGL.prod₂Equiv (GlobalTheory.PrinSat.oneEquiv μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h1))
    (GlobalTheory.PrinSat.oneEquiv μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h2))).trans (E1.trans E2)
  have hA : Fin.append (fun _ : Fin 1 => μ₁) (fun _ : Fin 1 => μ₂) = fun i =>
      GlobalTheory.SmGL.unrChar (w.adicCompletion E) (![μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)),
        μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))] i) := by
    funext i
    fin_cases i
    · exact e1
    · exact e2
  have key := GlobalTheory.PrinSat.hasSatGL_prinSeries w ![μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)),
    μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))]
  rw [GlobalTheory.PrinSat.univ_map_two, ← hA] at key
  exact GlobalTheory.PrinSat.hasSatGL_of_equiv T key
