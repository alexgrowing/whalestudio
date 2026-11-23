import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.CuspRep Formalism.L2.Host
open GlobalTheory.ContraPair (barK invTOp Paired)
open scoped ContDiff

namespace UpperTheory.V.TC

open InvT

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem infGL_invT (y : GL (Fin a) (Cinf E)) : infGL E a (invT a _ y) = invT a (Ad E) (infGL E a y) := cornerGL_invT _ y

theorem chart_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun y => φ (invT a (Ad E) y)) g x = chart φ (invT a (Ad E) g) (invTL x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [invTL_val, chart_val, chart_val, map_mul, infGL_invT]

theorem invT_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun y => φ (invT a (Ad E) y)) ∈ Sm E a := fun g =>
  ((hφ (invT a (Ad E) g)).comp (fun _ hx => (contDiffAt_invTL hx).contDiffWithinAt) fun _ hx => isUnit_invTL hx).congr
    fun _ hx => chart_invT φ g hx

variable (E a) in

def dualFn : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun y => φ.1 (invT a (Ad E) y), invT_mem_Sm φ.2⟩
  invFun φ := ⟨fun y => φ.1 (invT a (Ad E) y), invT_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun x => congrArg φ.1 (invT_invT x)
  right_inv φ := Subtype.ext <| funext fun x => congrArg φ.1 (invT_invT x)

@[simp] theorem dualFn_apply (φ : Sm E a) (g : GA E a) : (dualFn E a φ).1 g = φ.1 (invT a (Ad E) g) := rfl

@[simp] theorem dualFn_dualFn (φ : Sm E a) : dualFn E a (dualFn E a φ) = φ := (dualFn E a).left_inv φ

theorem rt_dualFn (h : GA E a) (φ : Sm E a) : rt E a h (dualFn E a φ) = dualFn E a (rt E a (invT a (Ad E) h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (invT a (Ad E)) g h)

theorem lie_dualFn (X : Lie E a) (φ : Sm E a) :
    lie E a X (dualFn E a φ) = dualFn E a (lie E a (toL (-(Matrix.of X)ᵀ)) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (dualFn E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (invT a (Ad E) g) ∘ invTL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_invT φ.1 g hx
  have e1 : invTL (oneL E a) = oneL E a := invTL_one
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, fderiv_comp _ (by rw [e1]; exact differentiableAt_chart φ.2 _)
    ((contDiffAt_invTL (x := oneL E a) isUnit_one).differentiableAt (by simp)), e1, ContinuousLinearMap.comp_apply]
  exact congrArg _ (fderiv_invTL_one X)

omit [IsTotallyComplex E] in
theorem invTOp_invTOp (o : Op E a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (invT_invT k)
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => star_star (k.1 i j)))
  | lie X => exact congrArg Op.lie (funext fun i => funext fun j => neg_neg (X i j))

omit [NumberField E] [IsTotallyComplex E] in

theorem invT_toUnits (k : Kinf E a) : invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := Units.ext rfl

theorem act_dualFn (o : Op E a) (φ : Sm E a) : act o (dualFn E a φ) = dualFn E a (act (invTOp o) φ) := by
  cases o with
  | fin k => exact (rt_dualFn (finGL E a k) φ).trans (by rw [← finGL_invT]; rfl)
  | cpt k => exact (rt_dualFn (infGL E a (Unitary.toUnits k)) φ).trans (by rw [← infGL_invT, invT_toUnits]; rfl)
  | lie X => exact lie_dualFn X φ

theorem Eop_dualFn (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (dualFn E a φ) = dualFn E a ((-Eop τ j i) φ) := by
  have h : ∀ x, lieS E a i j x (dualFn E a φ) = -dualFn E a (lieS E a j i x φ) := fun x => by
    rw [lieS_apply, lie_dualFn, lieS_apply, ← map_neg, ← LinearMap.neg_apply, ← map_neg]
    exact congrArg (fun m : Matrix (Fin a) (Fin a) (Cinf E) => dualFn E a (lie E a (toL (-m)) φ))
      (Matrix.transpose_single i j x)
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, h, map_neg, map_smul, map_sub]
  module

private theorem qdet_conj {V : Type} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] V) (X Y : Fin a → Fin a → Module.End ℂ V)
    (h : ∀ i j φ, X i j (e φ) = e (Y i j φ)) (u : ℂ) (φ : V) :
    Formalism.REAL.qdet X u (e φ) = e (Formalism.REAL.qdet Y u φ) := by
  have h0 : ∀ (z : Module.End ℂ V) ψ, (e.conjAlgEquiv ℂ).toAlgHom z (e ψ) = e (z ψ) := fun z ψ =>
    congrArg (fun x => e (z x)) (e.symm_apply_apply ψ)
  have e1 : (fun i j => (e.conjAlgEquiv ℂ).toAlgHom (Y i j)) = X := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := e.surjective ψ
    rw [h0, h]
  rw [← h0, map_qdet, e1]

private theorem qdet_dual {V : Type} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] V) (X : Fin a → Fin a → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (h : ∀ i j φ, X i j (e φ) = e ((-X j i) φ)) (u : ℂ) (φ : V) :
    Formalism.REAL.qdet X (u + ((a : ℂ) - 1) / 2) (e φ) =
      (-1 : ℂ) ^ a • e (Formalism.REAL.qdet X (-u + ((a : ℂ) - 1) / 2) φ) := by
  rw [qdet_conj e X (fun i j => -X j i) h, Formalism.HermitianLatticeCounting.P.quantumDet_neg_transpose X hX,
    show (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2 by ring, LinearMap.smul_apply, map_smul]

theorem cap_dualFn (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (dualFn E a φ) = (-1 : ℂ) ^ a • dualFn E a (cap τ (-u) φ) :=
  qdet_dual (dualFn E a) (Eop τ) (glRel_Eop τ) (Eop_dualFn τ) u φ

theorem Zalg_dualFn {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (dualFn E a φ) = dualFn E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    have h : cap τ (-u) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, -u, rfl⟩
    exact ⟨_, Subalgebra.smul_mem (Zalg E a) h ((-1 : ℂ) ^ a), fun φ => by
      rw [cap_dualFn, LinearMap.smul_apply, map_smul]⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsTotallyComplex E] in

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a _ y) = height y := by
  unfold height
  rw [invT_val, invT_inv_val, InvT.norm_transpose, InvT.norm_transpose, add_right_comm]

theorem isAutForm_dualFn {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (dualFn E a φ) where
  left γ g := by rw [dualFn_apply, dualFn_apply, map_mul, ← ratGL_invT, h.left]
  level := by
    convert h.level.preimage (continuous_invT (R := Af E) (a := a)) using 1
    ext k
    exact (Iff.of_eq (congrArg (· = dualFn E a φ) (act_dualFn (.fin k) φ))).trans (dualFn E a).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (dualFn E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_dualFn (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (dualFn E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_dualFn hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (invT a (Ad E) g)
    refine ⟨C, N, fun y => ?_⟩
    rw [dualFn_apply, map_mul, ← infGL_invT, ← height_invT]
    exact h1 _

theorem isCuspForm_dualFn {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (dualFn E a φ) :=
  ⟨isAutForm_dualFn h.1, isCuspidal_invT h.1.left h.2⟩

theorem dualFn_mulChi (χ : HChar E) (φ : Sm E a) : dualFn E a (mulChi a χ φ) = mulChi a χ⁻¹ (dualFn E a φ) :=
  Subtype.ext <| funext fun g => by simp only [dualFn_apply, mulChi_apply, chiDet_invT]

variable (π : CuspSub E a)

def dual : CuspSub E a where
  V := π.V.map (dualFn E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact isCuspForm_dualFn (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_dualFn o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := dualFn E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (dualFn E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (dualFn E a).injective h2]) fun o φ hφ => by
      have h1 := hs (invTOp o) _ hφ
      change act _ (dualFn E a φ) ∈ W at h1
      rw [act_dualFn, invTOp_invTOp] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective (f := (dualFn E a).toLinearMap) (dualFn E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem mem_dual {φ : Sm E a} : φ ∈ (dual π).V ↔ dualFn E a φ ∈ π.V :=
  ⟨fun ⟨ψ, h, e⟩ => by rw [← e]; exact (dualFn_dualFn ψ).symm ▸ h, fun h => ⟨_, h, dualFn_dualFn φ⟩⟩

def toDual : π.V ≃ₗ[ℂ] (dual π).V := (dualFn E a).submoduleMap π.V

@[simp] theorem toDual_val (φ : π.V) : (toDual π φ).1 = dualFn E a φ.1 := rfl

theorem op_toDual (o : Op E a) (φ : π.V) : (dual π).op o (toDual π φ) = toDual π (π.op (invTOp o) φ) :=
  Subtype.ext (act_dualFn o φ.1)

theorem finPart_toDual (k : GL (Fin a) (Af E)) (φ : π.V) :
    (dual π).finPart k (toDual π φ) = toDual π (π.finPart (invT a (Af E) k) φ) := op_toDual π (.fin k) φ

theorem locRep_toDual (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) (φ : π.V) :
    (dual π).locRep w g (toDual π φ) = toDual π (π.locRep w (invT a _ g) φ) :=
  (finPart_toDual π (locGL E a w g) φ).trans (by rw [← locGL_invT]; rfl)

@[simp] theorem dual_dual : dual (dual π) = π := CuspSub.ext <| by
  ext φ
  rw [mem_dual, mem_dual, dualFn_dualFn]

theorem dual_twist (χ : HChar E) : dual (π.twist χ) = (dual π).twist χ⁻¹ := CuspSub.ext <| by
  change (π.V.map _).map _ = (π.V.map _).map _
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  exact congrArg (fun f => π.V.map f) (LinearMap.ext (dualFn_mulChi χ))

variable {π} {π' : CuspSub E a}

theorem iso_dual (h : π.Iso π') : (dual π).Iso (dual π') := by
  obtain ⟨T, hT⟩ := h
  refine ⟨((toDual π).symm.trans T).trans (toDual π'), fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := (toDual π).surjective φ
  simp only [op_toDual, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hT]

theorem hasInfChar_dual {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) :
    (dual π).HasInfChar τ (m.map Neg.neg) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (dualFn E a φ) = _ • dualFn E a φ
  rw [cap_dualFn, h.2 _ φ hφ, map_smul, smul_smul, Multiset.map_map]
  congr 1
  rw [← h.1, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 2
  funext z
  simp only [Function.comp_apply]; ring

theorem hasSatGL_dual {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((dual π).locRep w) (B.map (·⁻¹)) :=
  hasSatGL_invT (toDual π) (locRep_toDual π w) h

theorem isLocComp_dual {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) : (dual π).IsLocComp w (smIrrInvT σ) := by
  obtain ⟨f, h0, hf⟩ := h
  refine ⟨(toDual π).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (toDual π).injective ?_), fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change toDual π (f (σ.ρ (invT a _ g) v)) = (dual π).locRep w g (toDual π (f v))
    rw [locRep_toDual]
    exact congrArg _ (hf _ v)

theorem hasFixed_dual {U : Subgroup (GL (Fin a) (Af E))} (hU : ∀ u ∈ U, invT a (Af E) u ∈ U)
    (h : Af.HasFixed π.finPart U) : Af.HasFixed (dual π).finPart U :=
  hasFixed_invT (toDual π) (finPart_toDual π) hU h

theorem hasFixed_KLev_dual {M : ℕ} (h : Af.HasFixed π.finPart (Af.KLev E a M)) :
    Af.HasFixed (dual π).finPart (Af.KLev E a M) := hasFixed_dual (fun _ => invT_mem_KLev) h

theorem hasSat_dual {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) :
    (CG.mk (dual π)).HasSat w (B.map (·⁻¹)) := hasSatGL_dual h

theorem paired_dual (h : Paired π π' invTOp) : Paired π (dual π') id := by
  obtain ⟨B, h1, h2, hf, hc, hl⟩ := h
  have e : ∀ o ψ, (toDual π').symm ((dual π').op o ψ) = π'.op (invTOp o) ((toDual π').symm ψ) := fun o ψ => by
    obtain ⟨ψ, rfl⟩ := (toDual π').surjective ψ
    rw [op_toDual, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨B.compl₂ (toDual π').symm.toLinearMap, fun φ h => h1 φ fun ψ => by simpa using h (toDual π' ψ),
    fun ψ h => (map_eq_zero_iff _ (toDual π').symm.injective).1 (h2 _ h), fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (congrArg (B _) (e _ ψ)).trans (hf k φ _)
  · exact (congrArg (B _) (e _ ψ)).trans (hc k φ _)
  · exact (congrArg (fun y => _ + B _ y) (e _ ψ)).trans (hl X φ _)

def dualCG (π : CG E a) : CG E a :=
  Quotient.map (sa := CuspSub.setoid E a) (sb := CuspSub.setoid E a) dual (fun _ _ h => iso_dual h) π

@[simp] theorem dualCG_mk (π : CuspSub E a) : dualCG (CG.mk π) = CG.mk (dual π) := rfl

end UpperTheory.V.TC
