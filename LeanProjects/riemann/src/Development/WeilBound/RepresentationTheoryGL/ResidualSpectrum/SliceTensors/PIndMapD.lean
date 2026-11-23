import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalSum
import GroundTheory.PAdicHodge.ACrisBdR

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def res (y : GA E (r + s)) : (GA E (r + s) → ℂ) →ₗ[ℂ] (GA E r × GA E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => lev (Ad E) r s m * y

theorem res_apply (y : GA E (r + s)) (F : GA E (r + s) → ℂ) (m : GA E r × GA E s) :
    res y F m = F (lev (Ad E) r s m * y) := rfl

structure Good (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r)
    (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Prop where
  hU₁ : IsStable U₁
  hU₂ : IsStable U₂
  hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)
  hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)

theorem good_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂) :
    Good U₁ U₂ LinearMap.id LinearMap.id :=
  ⟨hU₁, hU₂, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def IsInd (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (F : GA E (r + s) → ℂ) : Prop :=
  (∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x) ∧ ∀ k g, res (cf (r + s) k g) F ∈ tens2 U₁ U₂

def indSub (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | IsInd U₁ U₂ F.1}
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change F.1 _ + G.1 _ = F.1 x + G.1 x
      rw [hF.1, hG.1]
    · exact add_mem (hF.2 k g) (hG.2 k g)
  zero_mem' := by
    exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' := by
    intro c F hF
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change c * F.1 _ = c * F.1 x
      rw [hF.1]
    · exact Submodule.smul_mem _ c (hF.2 k g)

theorem exists_dec (x : GA E (r + s)) :
    ∃ q : (BlockIx (r + s) r → Ad E) × (GA E r × GA E s) × Kinf E (r + s) × GL (Fin (r + s)) (Af E),
      x = unip q.1 * lev (Ad E) r s q.2.1 * cf (r + s) q.2.2.1 q.2.2.2 := by
  obtain ⟨u, m, k, g, h⟩ := exists_decomp x
  exact ⟨(u, m, k, g), h⟩

def ind (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E (r + s) → ℂ) :=
  LinearMap.pi fun x => LinearMap.proj (exists_dec x).choose.2.1 ∘ₗ tensOp f₁ f₂ ∘ₗ
    res (cf (r + s) (exists_dec x).choose.2.2.1 (exists_dec x).choose.2.2.2)

theorem cf_inv (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : (cf a k g)⁻¹ = cf a k⁻¹ g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [cf_mul, mul_inv_cancel, mul_inv_cancel, cf, map_one, map_one, map_one, mul_one]

theorem cf_one (a : ℕ) : cf a (1 : Kinf E a) 1 = 1 := by
  rw [cf, map_one, map_one, map_one, mul_one]

theorem D.unip_add' {R : Type} [CommRing R] {a r : ℕ} (x y : BlockIx a r → R) : unip (x + y) = unip x * unip y := by
  simp only [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_add x y

theorem D.indep {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    {u u' : BlockIx (r + s) r → Ad E} {m m' : GA E r × GA E s} {k k' : Kinf E (r + s)} {g g' : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m * cf (r + s) k g = unip u' * lev (Ad E) r s m' * cf (r + s) k' g') :
    tensOp f₁ f₂ (res (cf (r + s) k g) F) m = tensOp f₁ f₂ (res (cf (r + s) k' g') F) m' := by
  obtain ⟨v, hv⟩ := lev_mul_unip m⁻¹ (-u + u')
  have hu : unip (-u) * unip u = (1 : GA E (r + s)) := by rw [← D.unip_add', neg_add_cancel, unip_zero]
  have e1 : cf (r + s) k g = unip v * lev (Ad E) r s (m⁻¹ * m') * cf (r + s) k' g' := by
    rw [map_mul, ← mul_assoc, ← hv, D.unip_add']
    calc cf (r + s) k g = lev (Ad E) r s m⁻¹ * (unip (-u) * (unip u * lev (Ad E) r s m * cf (r + s) k g)) := by
          rw [← mul_assoc (unip (-u)), ← mul_assoc (unip (-u)), hu, one_mul, ← mul_assoc, ← map_mul, inv_mul_cancel,
            map_one, one_mul]
      _ = _ := by rw [h]; simp only [mul_assoc]
  have e2 : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (g * g'⁻¹) := by
    rw [← cf_mul, ← cf_inv, e1, mul_inv_cancel_right]
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf e2
  have e3 : res (cf (r + s) k g) F = fun z => res (cf (r + s) k' g') F (z.1 * cf r k₁ g₁, z.2 * cf s k₂ g₂) := by
    funext z
    obtain ⟨w, hw⟩ := lev_mul_unip z v
    rw [res_apply, res_apply, e1, ← mul_assoc, ← mul_assoc, hw, mul_assoc, mul_assoc, hF.1, ← mul_assoc, ← map_mul, hm]
    rfl
  rw [e3, tensOp_translate H.hU₁ H.hU₂ H.hf₁ H.hf₂ (hF.2 k' g')]
  have e4 : m' = (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
    rw [← mul_inv_cancel_left m m', hm]
    rfl
  rw [e4]

theorem ind_apply {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ind f₁ f₂ F (unip u * lev (Ad E) r s m * cf (r + s) k g) = tensOp f₁ f₂ (res (cf (r + s) k g) F) m := by
  have hq := (exists_dec (unip u * lev (Ad E) r s m * cf (r + s) k g)).choose_spec
  exact (D.indep H hF hq).symm

theorem ind_left {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (x : GA E (r + s)) : ind f₁ f₂ F (unip u * x) = ind f₁ f₂ F x := by
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [← mul_assoc, ← mul_assoc, ← D.unip_add', ind_apply H hF, ind_apply H hF]

theorem ind_levi {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    res (cf (r + s) k g) (ind f₁ f₂ F) = tensOp f₁ f₂ (res (cf (r + s) k g) F) := by
  funext m
  have := ind_apply H hF 0 m k g
  rw [unip_zero, one_mul] at this
  exact this

theorem isInd_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E (r + s) → ℂ}
    (hF : IsInd U₁ U₂ F) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    IsInd U₁ U₂ fun x => F (x * cf (r + s) k g) := by
  refine ⟨fun u x => by beta_reduce; rw [mul_assoc, hF.1], fun k' g' => ?_⟩
  convert hF.2 (k' * k) (g' * g) using 1
  funext m
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ind_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (x : GA E (r + s)) :
    ind f₁ f₂ (fun y => F (y * cf (r + s) k g)) x = ind f₁ f₂ F (x * cf (r + s) k g) := by
  obtain ⟨v, m, k', g', rfl⟩ := exists_decomp x
  rw [ind_apply H (isInd_rt hF k g), mul_assoc _ (cf (r + s) k' g'), cf_mul, ind_apply H hF]
  refine congrArg (fun G => tensOp f₁ f₂ G m) (funext fun z => ?_)
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ext_res {F F' : GA E (r + s) → ℂ} (hF : ∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x)
    (hF' : ∀ (u : BlockIx (r + s) r → Ad E) x, F' (unip u * x) = F' x)
    (e : ∀ k g, res (cf (r + s) k g) F = res (cf (r + s) k g) F') : F = F' := by
  funext x
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [mul_assoc, hF, hF']
  exact congrFun (e k g) m

theorem ind_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : IsStable U₁) (hU₂ : IsStable U₂)
    {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F) : ind LinearMap.id LinearMap.id F = F := by
  refine ext_res (ind_left (good_id hU₁ hU₂) hF) hF.1 fun k g => ?_
  rw [ind_levi (good_id hU₁ hU₂) hF, tensOp_id (hF.2 k g)]

theorem finVec_rt {F : Sm E (r + s)} (hF : F ∈ finVec (cptRep E (r + s))) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : rt E (r + s) (cf (r + s) k g) F ∈ finVec (cptRep E (r + s)) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)) := hF
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k' => cptRep E (r + s) k' (rt E (r + s) (cf (r + s) k g) F)))
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)).map
    (rt E (r + s) (finGL E (r + s) g))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k' * k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  change F.1 (x * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits (k' * k))) =
    F.1 (x * infGL E (r + s) (Unitary.toUnits k') * cf (r + s) k g)
  rw [cf, mul_assoc x, ← infGL_comm, map_mul, map_mul]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
