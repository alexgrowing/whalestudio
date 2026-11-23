import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {H : Subgroup G} (hH : IsCompact (H : Set G))

include hρ hH in

theorem idem_comm (T : Module.End ℂ V) (hT : ∀ g, T * ρ g = ρ g * T) (v : V) :
    T (GlobalTheory.LocGL.idem hρ hH v) = GlobalTheory.LocGL.idem hρ hH (T v) := by
  have h1 : v - GlobalTheory.LocGL.idem hρ hH v ∈ GlobalTheory.PRep.twKer ρ H 1 := (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).1 (by
    rw [map_sub, GlobalTheory.LocGL.idem_of_mem hρ hH (GlobalTheory.LocGL.idem_mem hρ hH v), sub_self])
  have h2 : T (v - GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.twKer ρ H 1 := by
    refine (Submodule.span_le (p := (GlobalTheory.PRep.twKer ρ H 1).comap T)).2 ?_ h1
    rintro _ ⟨n, w, rfl⟩
    refine Submodule.subset_span ⟨n, T w, ?_⟩
    rw [map_sub, map_smul]
    exact congrArg (· - _) (LinearMap.congr_fun (hT n) w)
  have h3 : T (GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.fixed ρ H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← Module.End.mul_apply, ← hT, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 (GlobalTheory.LocGL.idem_mem hρ hH v) k hk]
  rw [show T v = T (GlobalTheory.LocGL.idem hρ hH v) + T (v - GlobalTheory.LocGL.idem hρ hH v) by rw [← map_add, add_sub_cancel],
    map_add, GlobalTheory.LocGL.idem_of_mem hρ hH h3, (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).2 h2, add_zero]

end Gen

section Cusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem op_comm_fin (π : CuspSub E a) (o : Op E a) (ho : ∀ k, o ≠ .fin k) (g : GL (Fin a) (Af E)) (y : π.V) :
    π.op o (π.finPart g y) = π.finPart g (π.op o y) := by
  refine Subtype.ext ?_
  cases o with
  | fin k => exact (ho k rfl).elim
  | cpt u =>
    change (rt E a (infGL E a (Unitary.toUnits u)) * rt E a (finGL E a g)) y.1 =
      (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits u))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X => exact LinearMap.congr_fun (lie_rt_fin X g) y.1

theorem bot_or_top (π : CuspSub E a) (W : Submodule ℂ π.V) (h : ∀ o, ∀ x ∈ W, π.op o x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, h o x hx, rfl⟩) with e | e
  · exact Or.inl (hi (e.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (e.trans (Submodule.map_subtype_top _).symm))

end Cusp

end GlobalTheory.TwistRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_conj_mem {a : ℕ} (ha : 1 ≤ a) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (v.adicCompletion E))
    (u : (v.adicCompletion E)ˣ) (hu : IsUnitAt v u) :
    ∃ h ∈ GlobalTheory.LFun.KGL v a, g⁻¹ * h * g ∈ GlobalTheory.LFun.KGL v a ∧ GeneralLinearGroup.det h = u := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have hK : GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL v a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion v a
  obtain ⟨x, hx, y, hy, t, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT (n := Fin a) g
  rw [hK] at hx hy
  have hu1 : Valued.v (u : v.adicCompletion E) ≤ 1 := le_of_eq hu
  have hu2 : Valued.v ((u⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (u : v.adicCompletion E) = 1 from hu, inv_one]
  let u' : (Formalism.UG.Ov E v)ˣ := ⟨⟨u, hu1⟩, ⟨(u⁻¹ : (v.adicCompletion E)ˣ), hu2⟩,
    Subtype.ext (Units.mul_inv u), Subtype.ext (Units.inv_mul u)⟩
  let i₀ : Fin a := ⟨0, ha⟩
  let d := GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) (Pi.mulSingle i₀ u)
  have hd : d ∈ GlobalTheory.LFun.KGL v a := by
    refine ⟨GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u'), Units.ext ?_⟩
    change ((Formalism.UG.Ov E v).subtype.mapMatrix (GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u')).val :
      Matrix (Fin a) (Fin a) (v.adicCompletion E)) = (d : Matrix (Fin a) (Fin a) (v.adicCompletion E))
    rw [GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi; simp [u']
      · simp [hi]
    · simp [hij]
  have hdt : (GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t)⁻¹ * d * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t = d := by
    rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  refine ⟨x * d * x⁻¹, mul_mem (mul_mem hx hd) (inv_mem hx), ?_, ?_⟩
  · have e : (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y)⁻¹ * (x * d * x⁻¹) *
        (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y) = y⁻¹ * d * y := by
      conv_rhs => rw [← hdt]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hy) hd) hy
  · have hdet : GeneralLinearGroup.det d = u := by
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal]
      rw [Finset.prod_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp
    rw [map_mul, map_mul, map_inv, hdet, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_locGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (Af E))
    (h : GL (Fin a) (v.adicCompletion E)) :
    g⁻¹ * locGL E a v h * g = locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
      GeneralLinearGroup.map (pLoc E v) g) := by
  have key : ∀ w, GeneralLinearGroup.map (pLoc E w) (g⁻¹ * locGL E a v h * g) =
      GeneralLinearGroup.map (pLoc E w) (locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g)) := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, map_mul, map_mul, map_inv, pLoc_locGL]
    · rw [pLoc_locGL_of_ne hw, map_mul, map_mul, pLoc_locGL_of_ne hw, mul_one, map_inv, inv_mul_cancel]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun w => ?_)
  exact congrArg (fun M : GL (Fin a) (w.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
    (key w)

end Local

end GlobalTheory.TwistRamified

namespace GlobalTheory.TwistRamified

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem no_eigvec (p : CuspSub E a) (ha : 1 ≤ a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (hη : ¬ η.UnrAt v)
    {x : p.V} (hx : x ∈ GlobalTheory.PRep.fixed (p.locRep v) (GlobalTheory.LFun.KGL v a)) (hx0 : x ≠ 0) (y : p.V)
    (hy : ∀ k ∈ GlobalTheory.LFun.KGL v a, p.locRep v k y = ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • y) : y = 0 := by
  set χ := CuspSub.locDet a η v with hχdef
  have hχs : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := GlobalTheory.SmGL.IsSmoothChar.inv (CuspSub.isOpen_ker_locDet (a := a) η v)
  have hρ := p.isSmooth_locRep v
  have hρ' := GlobalTheory.SmGL.isSmooth_twist hρ hχs
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v a).2
  set P := GlobalTheory.LocGL.idem hρ' hK with hPdef
  have hρ'app : ∀ g z, GlobalTheory.SmGL.twist (p.locRep v) χ⁻¹ g z = ((χ g : ℂˣ) : ℂ)⁻¹ • p.locRep v g z := fun g z => by
    simp

  have hPeq : ∀ k ∈ GlobalTheory.LFun.KGL v a, ∀ z, P (p.locRep v k z) = ((χ k : ℂˣ) : ℂ) • P z := fun k hk z => by
    have h1 := GlobalTheory.LocGL.idem_apply_mem hρ' hK hk z
    rw [hρ'app, map_smul] at h1
    rw [← h1, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hPfix : P y = y := by
    refine GlobalTheory.LocGL.idem_of_mem hρ' hK (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_)
    rw [hρ'app, hy k hk, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hPzero : ∀ z, ∀ h ∈ GlobalTheory.LFun.KGL v a, χ h ≠ 1 → p.locRep v h z = z → P z = 0 := fun z h hh hc hz => by
    have h1 := hPeq h hh z
    rw [hz] at h1
    have h2 : (((χ h : ℂˣ) : ℂ) - 1) • P z = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    refine (smul_eq_zero.1 h2).resolve_left fun h0 => hc (Units.ext ?_)
    rw [Units.val_one]; exact sub_eq_zero.1 h0

  have hPcomm : ∀ o : Op E a, (∀ k, o ≠ .fin k) → ∀ z, P (p.op o z) = p.op o (P z) := fun o ho z => by
    have h1 := idem_comm hρ' hK (p.op o) (fun g => by
      refine LinearMap.ext fun w => ?_
      simp only [Module.End.mul_apply, hρ'app, map_smul]
      congr 1
      exact op_comm_fin p o ho (locGL E a v g) w) z
    exact h1.symm

  have hPx : ∀ g : GL (Fin a) (Af E), P (p.finPart g x) = 0 := fun g => by
    obtain ⟨u, hu, hu1⟩ : ∃ u, IsUnitAt v u ∧ η.loc v u ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hη hc
    obtain ⟨h, hh, hgh, hdet⟩ := exists_conj_mem ha v (GeneralLinearGroup.map (pLoc E v) g) u hu
    refine hPzero _ h hh (by rw [hχdef, CuspSub.locDet, MonoidHom.comp_apply, hdet]; exact hu1) ?_
    have e : locGL E a v h * g = g * locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g) := by
      rw [← conj_locGL]; group
    change p.finPart (locGL E a v h) (p.finPart g x) = _
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    congr 1
    exact GlobalTheory.LGrp.mem_fixed.1 hx _ hgh

  let W : Submodule ℂ p.V :=
    { carrier := {φ | ∀ g, P (p.finPart g φ) = 0}
      add_mem' := fun {φ ψ} hφ hψ g => by rw [map_add, map_add, hφ g, hψ g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c φ hφ g => by
        change P (p.finPart g (c • φ)) = 0
        rw [map_smul, map_smul, hφ g, smul_zero] }
  have hW : ∀ o, ∀ φ ∈ W, p.op o φ ∈ W := by
    intro o φ hφ g
    by_cases ho : ∀ k, o ≠ .fin k
    · rw [← op_comm_fin p o ho, hPcomm o ho]
      change p.op o (P (p.finPart g φ)) = 0
      rw [hφ g, map_zero]
    · push_neg at ho
      obtain ⟨k, rfl⟩ := ho
      have e : p.finPart g (p.op (.fin k) φ) = p.finPart (g * k) φ := by
        rw [map_mul, Module.End.mul_apply]; rfl
      rw [e]
      exact hφ (g * k)
  rcases bot_or_top p W hW with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (show x ∈ W from hPx))) hx0
  · have h1 : y ∈ W := h ▸ Submodule.mem_top
    have h2 := h1 1
    rwa [map_one, Module.End.one_apply, hPfix] at h2

end GlobalTheory.TwistRamified

open GlobalTheory.CuspRep in

theorem GlobalTheory.TwistRamified.twist_ne : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v →
    π.twist η ≠ π := by
  intro E _ _ _ a ha π η v B hB hη
  induction π using Quotient.inductionOn with | _ p => ?_
  intro e
  obtain ⟨T, hT⟩ : CuspSub.Iso (p.twist η) p := Quotient.exact e
  have hB' : GlobalTheory.LFun.HasSatGL v (p.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL v a, p.locRep v k (T (p.toTwist η x)) =
      ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • T (p.toTwist η x) := fun k hk => by
    rw [CuspSub.locRep_eq, ← hT, CuspSub.op_toTwist, ← CuspSub.locRep_eq, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
    simp only [opAdd, zero_smul, add_zero, map_smul]
    congr 2
    exact CuspSub.chiDet_locGL η v k
  have h0 := GlobalTheory.TwistRamified.no_eigvec p ha η v hη hx hx0 _ hy
  exact hx0 ((p.toTwist η).injective (T.injective (h0.trans (map_zero T).symm) |>.trans (map_zero _).symm))
