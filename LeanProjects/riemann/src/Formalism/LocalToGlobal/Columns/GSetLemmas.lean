import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.ThetaLiftIndependence.Statement
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.DivisionValues Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace GSD

variable (S : GSD K)

theorem wt_eq (h : S.Ok) (s : S.Sec) (c : S.Cl) :
    (S.toCSDOf h s).wt c = Nat.card (MulAction.stabilizer S.G (s.rep c)) := by
  unfold CSD.wt
  exact Fintype.card_eq_nat_card

theorem card_stab_smul (g : S.G) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (g • d)) = Nat.card (MulAction.stabilizer S.G d) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * (x : S.G) * g, ?_⟩
      invFun := fun y => ⟨g * (y : S.G) * g⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp x.2, inv_smul_smul]
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.mp y.2]
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])

theorem ipOf_eq_sum (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : K))⁻¹ * S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  unfold ipOf CSD.csum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [S.wt_eq h s c]

theorem mem_intOf_iff (N : S.D → Submodule (𝓞 K) S.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K))) (s : S.Sec)
    (φ : S.EqFun) : φ ∈ S.intOf N ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ N (s.rep c) := by
  constructor
  · intro hφ c
    exact hφ (s.rep c)
  · intro hφ d
    have e := s.mv_smul d
    rw [← e, φ.2, hN]
    exact Submodule.mem_map_of_mem (hφ (S.cls d))

theorem mem_intNab_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intNab ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Nab (s.rep c) := by
  exact S.mem_intOf_iff S.Nab h.nab_smul s φ

theorem mem_intDel_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Del (s.rep c) := by
  exact S.mem_intOf_iff S.Del h.del_smul s φ

def coordOf (h : S.Ok) (s : S.Sec) : S.EqFun ≃ₗ[K] (Fin (S.toCSDOf h s).dim → K) :=
  (S.resOf h s).trans (S.toCSDOf h s).basis.equivFun

theorem I_coordOf (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    (S.toCSDOf h s).I (S.coordOf h s φ) = fun c => (φ : S.D → S.V) (s.rep c) := by
  show (((S.toCSDOf h s).basis.equivFun.symm ((S.toCSDOf h s).basis.equivFun (S.resOf h s φ)) :
    (S.toCSDOf h s).Forms) : S.Cl → S.V) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem coordOf_mem_nabLat (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    S.coordOf h s φ ∈ (S.toCSDOf h s).nabLat ↔ φ ∈ S.intNab := by
  unfold CSD.nabLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intNab_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩

theorem coordOf_mem_delLat (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    S.coordOf h s φ ∈ (S.toCSDOf h s).delLat ↔ φ ∈ S.intDel := by
  unfold CSD.delLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intDel_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩

theorem map_intNab (h : S.Ok) (s : S.Sec) :
    S.intNab.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).nabLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_nabLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_nabLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp

theorem map_intDel (h : S.Ok) (s : S.Sec) :
    S.intDel.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).delLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_delLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_delLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp

theorem ipOf_coord (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = hform (S.toCSDOf h s).H (S.coordOf h s φ) (S.coordOf h s ψ) := by
  have e := (S.toCSDOf h s).csum_sum (S.coordOf h s φ) (S.coordOf h s ψ)
  rw [S.I_coordOf, S.I_coordOf] at e
  unfold ipOf
  rw [e]
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem finrank_EqFun (h : S.Ok) (s : S.Sec) : finrank K S.EqFun = (S.toCSDOf h s).dim := by
  unfold CSD.dim
  exact (S.resOf h s).finrank_eq

theorem finiteDimensional_EqFun (h : S.Ok) : FiniteDimensional K S.EqFun := by
  letI := h.fintypeCl
  haveI : Module.Finite K S.V := Module.Finite.of_basis S.bV
  exact LinearEquiv.finiteDimensional (S.resOf h S.outSec).symm

variable {S} in
theorem Sec.exists_smul (s s' : S.Sec) (c : S.Cl) : ∃ g : S.G, g • s.rep c = s'.rep c := by
  exact (S.cls_eq_iff _ _).mp ((s'.spec c).trans (s.spec c).symm)

theorem ipOf_indep (h : S.Ok) (s s' : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ipOf h s' φ ψ := by
  rw [S.ipOf_eq_sum h s, S.ipOf_eq_sum h s']
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [← hg, φ.2, ψ.2, h.inv, card_stab_smul]

theorem ipOf_eq_ip (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ip h φ ψ := by
  exact (S.ipOf_indep h s S.outSec φ ψ).trans rfl

theorem dim_indep (h : S.Ok) (s s' : S.Sec) : (S.toCSDOf h s).dim = (S.toCSDOf h s').dim := by
  unfold CSD.dim
  exact ((S.resOf h s).symm.trans (S.resOf h s')).finrank_eq

def chgSec (h : S.Ok) (s s' : S.Sec) : (S.toCSDOf h s).Forms ≃ₗ[K] (S.toCSDOf h s').Forms :=
  (S.resOf h s).symm.trans (S.resOf h s')

theorem chgSec_csum (h : S.Ok) (s s' : S.Sec) (f f' : (S.toCSDOf h s).Forms) :
    (S.toCSDOf h s').csum (S.chgSec h s s' f).1 (S.chgSec h s s' f').1 = (S.toCSDOf h s).csum f.1 f'.1 := by
  have e1 := S.ipOf_indep h s s' ((S.resOf h s).symm f) ((S.resOf h s).symm f')
  have e2 : ∀ g : (S.toCSDOf h s).Forms,
      (fun c => (((S.resOf h s).symm g : S.EqFun) : S.D → S.V) (s.rep c)) = (g : S.Cl → S.V) :=
    fun g => congrArg Subtype.val ((S.resOf h s).apply_symm_apply g)
  unfold ipOf at e1
  rw [e2 f, e2 f'] at e1
  exact e1.symm

theorem chgSec_nab (h : S.Ok) (s s' : S.Sec) (f : (S.toCSDOf h s).Forms) :
    (∀ c, (S.chgSec h s s' f).1 c ∈ S.Nab (s'.rep c)) ↔ ∀ c, f.1 c ∈ S.Nab (s.rep c) := by
  have e2 : f.1 = fun c => (((S.resOf h s).symm f : S.EqFun) : S.D → S.V) (s.rep c) :=
    (congrArg Subtype.val ((S.resOf h s).apply_symm_apply f)).symm
  rw [e2]
  exact (S.mem_intNab_iff h s' ((S.resOf h s).symm f)).symm.trans (S.mem_intNab_iff h s ((S.resOf h s).symm f))

end GSD

namespace ClsKer

variable {S S' : GSD K} (A : ClsKer S S')

theorem term_smul (φ : S.EqFun) (g : S.G) (d : S.D) (d' : S'.D) :
    A.k (g • d) d' ((φ : S.D → S.V) (g • d)) = A.k d d' ((φ : S.D → S.V) d) := by
  have e1 : ∀ y, S.ρ g⁻¹ (S.ρ g y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h1 := A.equiv g 1 d d'
  rw [one_smul, map_one] at h1
  rw [h1, φ.2]
  simp only [LinearMap.comp_apply, Module.End.one_apply, e1]

theorem appOf_indep (h : S.Ok) (s s' : S.Sec) (φ : S.EqFun) : A.appOf h s φ = A.appOf h s' φ := by
  funext d'
  unfold appOf
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := GSD.Sec.exists_smul s s' c
  rw [S.wt_eq h s c, S.wt_eq h s' c, ← hg, S.card_stab_smul, A.term_smul]

theorem opOf_indep (h : S.Ok) (s s' : S.Sec) : A.opOf h s = A.opOf h s' := by
  exact LinearMap.ext fun φ => Subtype.ext (A.appOf_indep h s s' φ)

theorem resOf_opOf (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) :
    (S'.resOf h' s' (A.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((S.toCSDOf h s).wt c : K))⁻¹) (A.atReps s s') (S.resOf h s φ).1 := rfl

end ClsKer

namespace GSD

variable (S : GSD K)

def Free : Prop := ∀ (d : S.D) (g : S.G), g • d = d → g = 1

theorem forms_eq_top (h : S.Ok) (s : S.Sec) (hf : S.Free) : (S.toCSDOf h s).Forms = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  intro c γ
  have hγ : ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) = 1 :=
    hf _ _ (MulAction.mem_stabilizer_iff.mp γ.2)
  show S.ρ ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) (f c) = f c
  rw [hγ, map_one, Module.End.one_apply]

theorem wt_eq_one (h : S.Ok) (s : S.Sec) (hf : S.Free) (c : S.Cl) : (S.toCSDOf h s).wt c = 1 := by
  rw [S.wt_eq h s c, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
  rw [hf _ _ (MulAction.mem_stabilizer_iff.mp a.2), hf _ _ (MulAction.mem_stabilizer_iff.mp b.2)]

def resFree (h : S.Ok) (s : S.Sec) (hf : S.Free) : S.EqFun ≃ₗ[K] (S.Cl → S.V) :=
  (S.resOf h s).trans (LinearEquiv.ofTop _ (S.forms_eq_top h s hf))

theorem resFree_apply (h : S.Ok) (s : S.Sec) (hf : S.Free) (φ : S.EqFun) (c : S.Cl) :
    S.resFree h s hf φ c = (φ : S.D → S.V) (s.rep c) := rfl

theorem ipOf_free (h : S.Ok) (s : S.Sec) (hf : S.Free) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  rw [S.ipOf_eq_sum h s]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← S.wt_eq h s c, S.wt_eq_one h s hf c]
  simp only [Nat.cast_one, inv_one, one_mul]

theorem map_intNab_free (h : S.Ok) (s : S.Sec) (hf : S.Free) :
    S.intNab.map ((S.resFree h s hf : S.EqFun →ₗ[K] (S.Cl → S.V)).restrictScalars (𝓞 K)) =
      Submodule.pi Set.univ fun c => S.Nab (s.rep c) := by
  ext f
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    rw [Submodule.mem_pi]
    intro c _
    exact hφ (s.rep c)
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.resFree h s hf).symm f, ?_, ?_⟩
    · rw [S.mem_intNab_iff h s]
      intro c
      rw [← S.resFree_apply h s hf, LinearEquiv.apply_symm_apply]
      exact (Submodule.mem_pi.mp hx) c (Set.mem_univ c)
    · simp

theorem map_intDel_free (h : S.Ok) (s : S.Sec) (hf : S.Free) :
    S.intDel.map ((S.resFree h s hf : S.EqFun →ₗ[K] (S.Cl → S.V)).restrictScalars (𝓞 K)) =
      Submodule.pi Set.univ fun c => S.Del (s.rep c) := by
  ext f
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    rw [Submodule.mem_pi]
    intro c _
    exact hφ (s.rep c)
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.resFree h s hf).symm f, ?_, ?_⟩
    · rw [S.mem_intDel_iff h s]
      intro c
      rw [← S.resFree_apply h s hf, LinearEquiv.apply_symm_apply]
      exact (Submodule.mem_pi.mp hx) c (Set.mem_univ c)
    · simp

theorem finrank_free (h : S.Ok) (hf : S.Free) : finrank K S.EqFun = Nat.card S.Cl * finrank K S.V := by
  letI := h.fintypeCl
  haveI : Module.Finite K S.V := Module.Finite.of_basis S.bV
  rw [(S.resFree h S.outSec hf).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card]

end GSD

namespace GSD.Iso

variable {S S' : GSD K} (e : GSD.Iso S S')

theorem symm_smul (g' : S'.G) (d' : S'.D) : e.eD.symm (g' • d') = e.eG.symm g' • e.eD.symm d' := by
  rw [Equiv.symm_apply_eq, e.smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem onCl_cls (d : S.D) : e.onCl (S.cls d) = S'.cls (e.eD d) := rfl

def stabEquiv (d : S.D) : MulAction.stabilizer S.G d ≃ MulAction.stabilizer S'.G (e.eD d) :=
  Equiv.subtypeEquiv e.eG.toEquiv fun g => by
    show g ∈ MulAction.stabilizer S.G d ↔ e.eG g ∈ MulAction.stabilizer S'.G (e.eD d)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← e.smul, e.eD.apply_eq_iff_eq]

theorem card_stab (d : S.D) :
    Nat.card (MulAction.stabilizer S'.G (e.eD d)) = Nat.card (MulAction.stabilizer S.G d) := by
  exact Nat.card_congr (e.stabEquiv d).symm

theorem iso_integral_structure_equivariant (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K)))
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)))
    (g' : S'.G) (d' : S'.D) : N' (g' • d') = (N' d').map ((S'.ρ g').restrictScalars (𝓞 K)) := by
  obtain ⟨d, rfl⟩ := e.eD.surjective d'
  obtain ⟨g, rfl⟩ := e.eG.surjective g'
  rw [← e.smul, hc, hc, hN, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  exact e.rho g x

include e in

theorem ok (h : S.Ok) : S'.Ok where
  fin_orb := by
    have := h.fin_orb
    exact Finite.of_equiv _ e.onCl
  fin_stab := by
    intro d'
    obtain ⟨d, rfl⟩ := e.eD.surjective d'
    have := h.fin_stab d
    exact Finite.of_equiv _ (e.stabEquiv d)
  nab_smul := e.iso_integral_structure_equivariant S.Nab S'.Nab h.nab_smul e.nab
  del_smul := e.iso_integral_structure_equivariant S.Del S'.Del h.del_smul e.del
  inv := by
    intro g' x' y'
    obtain ⟨g, rfl⟩ := e.eG.surjective g'
    obtain ⟨x, rfl⟩ := e.eV.surjective x'
    obtain ⟨y, rfl⟩ := e.eV.surjective y'
    rw [← e.rho, ← e.rho, e.pair, e.pair, h.inv]

theorem iso_onForms_mem_integral_iff (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (φ : S.EqFun) :
    e.onForms φ ∈ S'.intOf N' ↔ φ ∈ S.intOf N := by
  constructor
  · intro hφ d
    have h1 : e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD d))) ∈ N' (e.eD d) := hφ (e.eD d)
    rw [Equiv.symm_apply_apply, hc] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    have hy' : y = (φ : S.D → S.V) d := e.eV.injective hxy
    rw [← hy']
    exact hy
  · intro hφ d'
    show e.eV ((φ : S.D → S.V) (e.eD.symm d')) ∈ N' d'
    have h2 := hc (e.eD.symm d')
    rw [Equiv.apply_symm_apply] at h2
    rw [h2]
    exact Submodule.mem_map_of_mem (hφ _)

theorem mem_intNab (φ : S.EqFun) : e.onForms φ ∈ S'.intNab ↔ φ ∈ S.intNab := by
  exact e.iso_onForms_mem_integral_iff S.Nab S'.Nab e.nab φ

theorem mem_intDel (φ : S.EqFun) : e.onForms φ ∈ S'.intDel ↔ φ ∈ S.intDel := by
  exact e.iso_onForms_mem_integral_iff S.Del S'.Del e.del φ

def mapSec (s : S.Sec) : S'.Sec where
  rep := fun c' => e.eD (s.rep (e.onCl.symm c'))
  spec := by
    intro c'
    rw [← e.onCl_cls, s.spec, Equiv.apply_symm_apply]

theorem ipOf_onForms (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ ψ : S.EqFun) :
    S'.ipOf h' s' (e.onForms φ) (e.onForms ψ) = S.ipOf h s φ ψ := by
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  rw [S'.ipOf_indep h' s' (e.mapSec s), GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Fintype.sum_equiv e.onCl.symm _ _ fun c' => ?_
  show ((Nat.card (MulAction.stabilizer S'.G (e.eD (s.rep (e.onCl.symm c')))) : K))⁻¹ *
    S'.pair (e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c'))))))
      (e.eV ((ψ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c')))))) = _
  rw [e.card_stab, Equiv.symm_apply_apply, e.pair]

include e in
theorem dim_eq (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (S'.toCSDOf h' s').dim = (S.toCSDOf h s).dim := by
  unfold CSD.dim
  exact (((S'.resOf h' s').symm.trans e.onForms.symm).trans (S.resOf h s)).finrank_eq

def coord (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (Fin (S.toCSDOf h s).dim → K) ≃ₗ[K] (Fin (S'.toCSDOf h' s').dim → K) :=
  ((S.coordOf h s).symm.trans e.onForms).trans (S'.coordOf h' s')

theorem hform_coord (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x y : Fin (S.toCSDOf h s).dim → K) :
    hform (S'.toCSDOf h' s').H (e.coord h h' s s' x) (e.coord h h' s s' y) = hform (S.toCSDOf h s).H x y := by
  have e1 := S'.ipOf_coord h' s' (e.onForms ((S.coordOf h s).symm x)) (e.onForms ((S.coordOf h s).symm y))
  have e2 := S.ipOf_coord h s ((S.coordOf h s).symm x) ((S.coordOf h s).symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e2
  rw [e.ipOf_onForms h h' s s'] at e1
  exact e1.symm.trans e2

theorem coord_mem_nabLat (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x : Fin (S.toCSDOf h s).dim → K) :
    e.coord h h' s s' x ∈ (S'.toCSDOf h' s').nabLat ↔ x ∈ (S.toCSDOf h s).nabLat := by
  show S'.coordOf h' s' (e.onForms ((S.coordOf h s).symm x)) ∈ _ ↔ _
  rw [S'.coordOf_mem_nabLat h' s', e.mem_intNab, ← S.coordOf_mem_nabLat h s, LinearEquiv.apply_symm_apply]

theorem coord_mem_delLat (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x : Fin (S.toCSDOf h s).dim → K) :
    e.coord h h' s s' x ∈ (S'.toCSDOf h' s').delLat ↔ x ∈ (S.toCSDOf h s).delLat := by
  show S'.coordOf h' s' (e.onForms ((S.coordOf h s).symm x)) ∈ _ ↔ _
  rw [S'.coordOf_mem_delLat h' s', e.mem_intDel, ← S.coordOf_mem_delLat h s, LinearEquiv.apply_symm_apply]

def refl (S : GSD K) : GSD.Iso S S where
  eG := MulEquiv.refl _
  eD := Equiv.refl _
  eV := LinearEquiv.refl _ _
  smul := fun _ _ => rfl
  rho := fun _ _ => rfl
  pair := fun _ _ => rfl
  nab := fun d => (Submodule.map_id (S.Nab d)).symm
  del := fun d => (Submodule.map_id (S.Del d)).symm
  rat := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rat_symm := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem transpose_form_mul_involution (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (d' : S'.D) :
    N (e.eD.symm d') = (N' d').map ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)) := by
  have h2 := hc (e.eD.symm d')
  rw [Equiv.apply_symm_apply] at h2
  have hid : ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)).comp
      ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)) = LinearMap.id := by
    ext x
    simp
  rw [h2, ← Submodule.map_comp, hid, Submodule.map_id]

def symm : GSD.Iso S' S where
  eG := e.eG.symm
  eD := e.eD.symm
  eV := e.eV.symm
  smul := e.symm_smul
  rho := by
    intro g' x'
    rw [LinearEquiv.symm_apply_eq, e.rho, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  pair := by
    intro x' y'
    rw [← e.pair, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  nab := e.transpose_form_mul_involution S.Nab S'.Nab e.nab
  del := e.transpose_form_mul_involution S.Del S'.Del e.del
  rat := e.rat_symm
  rat_symm := e.rat

theorem rat_comp {ι ι' ι'' V V' V'' : Type} [Fintype ι'] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] [AddCommGroup V''] [Module K V''] (b : Basis ι K V) (b' : Basis ι' K V') (b'' : Basis ι'' K V'')
    (f : V →ₗ[K] V') (f' : V' →ₗ[K] V'') (F : Subfield K) (h : ∀ i j, b'.repr (f (b j)) i ∈ F)
    (h' : ∀ i j, b''.repr (f' (b' j)) i ∈ F) (i : ι'') (j : ι) : b''.repr (f' (f (b j))) i ∈ F := by
  rw [← b'.sum_repr (f (b j))]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun k _ => mul_mem (h k j) (h' i k)

def trans {S'' : GSD K} (e' : GSD.Iso S' S'') : GSD.Iso S S'' where
  eG := e.eG.trans e'.eG
  eD := e.eD.trans e'.eD
  eV := e.eV.trans e'.eV
  smul := by
    intro g d
    show e'.eD (e.eD (g • d)) = e'.eG (e.eG g) • e'.eD (e.eD d)
    rw [e.smul, e'.smul]
  rho := by
    intro g x
    show e'.eV (e.eV (S.ρ g x)) = S''.ρ (e'.eG (e.eG g)) (e'.eV (e.eV x))
    rw [e.rho, e'.rho]
  pair := by
    intro x y
    show S''.pair (e'.eV (e.eV x)) (e'.eV (e.eV y)) = _
    rw [e'.pair, e.pair]
  nab := by
    intro d
    show S''.Nab (e'.eD (e.eD d)) = _
    rw [e'.nab, e.nab, ← Submodule.map_comp]
    rfl
  del := by
    intro d
    show S''.Del (e'.eD (e.eD d)) = _
    rw [e'.del, e.del, ← Submodule.map_comp]
    rfl
  rat := rat_comp S.bV S'.bV S''.bV (e.eV : S.V →ₗ[K] S'.V) (e'.eV : S'.V →ₗ[K] S''.V) (cmMax K) e.rat e'.rat
  rat_symm := rat_comp S''.bV S'.bV S.bV (e'.eV.symm : S''.V →ₗ[K] S'.V) (e.eV.symm : S'.V →ₗ[K] S.V) (cmMax K)
    e'.rat_symm e.rat_symm

end GSD.Iso

namespace LocOp

variable {S S' : GSD K}

theorem conj_eq_zero_iff (g : S.G) (g' : S'.G) (k : S.V →ₗ[K] S'.V) :
    (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g) = 0 ↔ k = 0 := by
  have e1 : ∀ y, S.ρ g (S.ρ g⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e2 : ∀ y, S'.ρ g'⁻¹ (S'.ρ g' y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  constructor
  · intro hk
    ext x
    have h1 := LinearMap.congr_fun hk (S.ρ g⁻¹ x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, e1] at h1
    have h2 := congrArg (S'.ρ g'⁻¹) h1
    rw [e2, map_zero] at h2
    rw [h2, LinearMap.zero_apply]
  · rintro rfl
    simp

theorem ker_eq_zero_iff (A : LocOp S S') (B : LocOp S' S) (hn : S.pair.Nondegenerate)
    (hn' : S'.pair.Nondegenerate)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y)) (d : S.D) (d' : S'.D) :
    A.ker d' d = 0 ↔ B.ker d d' = 0 := by
  constructor
  · intro hA
    ext y
    rw [LinearMap.zero_apply]
    refine hn.2 _ fun x => ?_
    rw [← hadj, hA, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  · intro hB
    ext x
    rw [LinearMap.zero_apply]
    refine hn'.1 _ fun y => ?_
    rw [hadj, hB, LinearMap.zero_apply, map_zero]

theorem adjoint (A : LocOp S S') (B : LocOp S' S) (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (hB : ∀ g, B.tr g = e g)
    (hsupp : ∀ d d', A.ker d' d = 0 ↔ B.ker d d' = 0)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' (A.app φ) ψ = S.ipOf h s φ (B.app ψ) := by
  classical
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  let act : MulAction S.G S'.D := MulAction.compHom S'.D (e : S.G →* S'.G)
  have hact : ∀ (γ : S.G) (b : S'.D), γ • b = e γ • b := fun _ _ => rfl
  have hstab : ∀ b : S'.D, (MulAction.stabilizer S.G b) ≃ (MulAction.stabilizer S'.G b) := fun b =>
    Equiv.subtypeEquiv e.toEquiv fun γ => Iff.rfl
  have hinj : Function.Injective s.rep := fun c c' hc => by rw [← s.spec c, hc, s.spec]
  have hinj' : Function.Injective s'.rep := fun c c' hc => by rw [← s'.spec c, hc, s'.spec]
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits S.G S.D S'.D K
    (fun a => (B.ker a).support) (fun b => (A.ker b).support)
    (fun a b => S.pair ((φ : S.D → S.V) a) (B.ker a b ((ψ : S'.D → S'.V) b)))
    (Finset.univ.image s.rep) (Finset.univ.image s'.rep)
    (by
      intro a b
      rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, not_iff_not]
      exact (hsupp a b).symm)
    (by
      intro γ a b hb
      rw [Finsupp.mem_support_iff] at hb ⊢
      rw [hact, ← hB, B.equiv, Ne, conj_eq_zero_iff]
      exact hb)
    (by
      intro γ a b _
      show S.pair ((φ : S.D → S.V) (γ • a)) (B.ker (γ • a) (γ • b) ((ψ : S'.D → S'.V) (γ • b))) = _
      rw [hact, ← hB, B.equiv, φ.2, ψ.2]
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply (S'.ρ (B.tr γ)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        h.inv])
    h.fin_stab
    (by
      intro b
      have := h'.fin_stab b
      exact Finite.of_equiv _ (hstab b).symm)
    (by
      intro a
      refine ⟨s.rep (S.cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact (S.cls_eq_iff _ _).mp (s.spec _)
      · rintro r ⟨hr, hr2⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : S.cls (s.rep c) = S.cls a := (S.cls_eq_iff _ _).mpr hr2
        rw [← h1, s.spec])
    (by
      intro b
      refine ⟨s'.rep (S'.cls b), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · obtain ⟨g', hg'⟩ := (S'.cls_eq_iff _ _).mp (s'.spec (S'.cls b))
        exact ⟨e.symm g', by show e (e.symm g') • b = _; rw [MulEquiv.apply_symm_apply, hg']⟩
      · rintro r ⟨hr, γ, hγ⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : S'.cls (s'.rep c) = S'.cls b := (S'.cls_eq_iff _ _).mpr ⟨e γ, hγ⟩
        rw [← h1, s'.spec])
  rw [Finset.sum_image (fun c _ c' _ hc => hinj hc), Finset.sum_image (fun c _ c' _ hc => hinj' hc)] at key
  rw [GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Eq.trans ?_ (key.symm.trans ?_)
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Nat.card_congr (hstab (s'.rep c')), Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    unfold app
    rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun d _ => hadj _ _ _ _
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    unfold app
    rw [Finsupp.sum, map_sum]

theorem adjoint_of_nondeg (A : LocOp S S') (B : LocOp S' S) (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (hB : ∀ g, B.tr g = e g) (hn : S.pair.Nondegenerate)
    (hn' : S'.pair.Nondegenerate)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' (A.app φ) ψ = S.ipOf h s φ (B.app ψ) := by
  exact A.adjoint B h h' e hB (fun d d' => A.ker_eq_zero_iff B hn hn' hadj d d') hadj s s' φ ψ

theorem ofNbr_adjoint (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (nb : S'.D → Finset S.D) (nb' : S.D → Finset S'.D) (T : S.V →ₗ[K] S'.V) (T' : S'.V →ₗ[K] S.V)
    (hn : ∀ g d' d, (e.symm : S'.G →* S.G) g • d ∈ nb (g • d') ↔ d ∈ nb d')
    (hT : ∀ g x, T (S.ρ ((e.symm : S'.G →* S.G) g) x) = S'.ρ g (T x))
    (hn' : ∀ g d d', (e : S.G →* S'.G) g • d' ∈ nb' (g • d) ↔ d' ∈ nb' d)
    (hT' : ∀ g x, T' (S'.ρ ((e : S.G →* S'.G) g) x) = S.ρ g (T' x))
    (htr : ∀ d d', d ∈ nb d' ↔ d' ∈ nb' d) (h0 : T = 0 ↔ T' = 0)
    (hadj : ∀ x y, S'.pair (T x) y = S.pair x (T' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' ((ofNbr (e.symm : S'.G →* S.G) nb T hn hT).op φ) ψ =
      S.ipOf h s φ ((ofNbr (e : S.G →* S'.G) nb' T' hn' hT').op ψ) := by
  classical
  have hk : ∀ d d', (ofNbr (e.symm : S'.G →* S.G) nb T hn hT).ker d' d = if d ∈ nb d' then T else 0 := by
    intro d d'
    show Finsupp.indicator (nb d') (fun _ _ => T) d = _
    rw [Finsupp.indicator_apply]
    by_cases hd : d ∈ nb d'
    · rw [dif_pos hd, if_pos hd]
    · rw [dif_neg hd, if_neg hd]
  have hk' : ∀ d d', (ofNbr (e : S.G →* S'.G) nb' T' hn' hT').ker d d' = if d ∈ nb d' then T' else 0 := by
    intro d d'
    show Finsupp.indicator (nb' d) (fun _ _ => T') d' = _
    rw [Finsupp.indicator_apply]
    by_cases hd : d ∈ nb d'
    · rw [dif_pos ((htr d d').mp hd), if_pos hd]
    · rw [dif_neg (fun H => hd ((htr d d').mpr H)), if_neg hd]
  refine adjoint _ _ h h' e (fun _ => rfl) ?_ ?_ s s' φ ψ
  · intro d d'
    rw [hk, hk']
    by_cases hd : d ∈ nb d'
    · rw [if_pos hd, if_pos hd, h0]
    · rw [if_neg hd, if_neg hd]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro d d' x y
    rw [hk, hk']
    by_cases hd : d ∈ nb d'
    · rw [if_pos hd, if_pos hd, hadj]
    · rw [if_neg hd, if_neg hd]
      simp

end LocOp

namespace GSD

variable (S : GSD K)

@[reducible] def restr (T : SubMulAction S.G S.D) : GSD K where
  G := S.G
  D := T
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab := fun t => S.Nab (t : S.D)
  Del := fun t => S.Del (t : S.D)

theorem restr_cls_eq_iff (T : SubMulAction S.G S.D) (t t' : T) :
    (S.restr T).cls t = (S.restr T).cls t' ↔ S.cls (t : S.D) = S.cls (t' : S.D) := by
  rw [GSD.cls_eq_iff, GSD.cls_eq_iff]
  exact exists_congr fun g => ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

theorem restr_card_stab (T : SubMulAction S.G S.D) (t : T) :
    Nat.card (MulAction.stabilizer (S.restr T).G (show (S.restr T).D from t)) =
      Nat.card (MulAction.stabilizer S.G (t : S.D)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

theorem restr_ok (h : S.Ok) (T : SubMulAction S.G S.D) : (S.restr T).Ok where
  fin_orb := by
    have := h.fin_orb
    let f : (S.restr T).Cl → S.Cl := fun c => S.cls (((S.restr T).outSec.rep c : T) : S.D)
    refine Finite.of_injective f fun c c' hc => ?_
    have h1 := (S.restr_cls_eq_iff T _ _).mpr hc
    rwa [(S.restr T).outSec.spec, (S.restr T).outSec.spec] at h1
  fin_stab := by
    intro t
    have := h.fin_stab ((t : T) : S.D)
    have E : MulAction.stabilizer S.G (t : T) ≃ MulAction.stabilizer S.G ((t : T) : S.D) :=
      Equiv.subtypeEquiv (Equiv.refl S.G) fun (g : S.G) =>
        (⟨fun H => congrArg Subtype.val H, fun H => Subtype.ext H⟩ :
          g • (t : T) = t ↔ g • ((t : T) : S.D) = ((t : T) : S.D))
    exact Finite.of_equiv _ E.symm
  nab_smul := fun g t => h.nab_smul g ((t : T) : S.D)
  del_smul := fun g t => h.del_smul g ((t : T) : S.D)
  inv := h.inv

variable (A : Type) [Group A] [MulAction A S.D]

structure Slice where
  T : SubMulAction S.G S.D
  uniq : ∀ d : S.D, ∃! a : A, a • d ∈ T

def FreeOnCl : Prop := ∀ (a : A) (d : S.D), S.cls (a • d) = S.cls d → a = 1

theorem exists_slice [SMulCommClass A S.G S.D] (hf : S.FreeOnCl A) : Nonempty (S.Slice A) := by
  have := SMulCommClass.symm A S.G S.D
  let r : Setoid S.D :=
    { r := fun d d' => ∃ (a : A) (g : S.G), a • g • d' = d
      iseqv :=
        { refl := fun d => ⟨1, 1, by rw [one_smul, one_smul]⟩
          symm := by
            rintro d d' ⟨a, g, rfl⟩
            exact ⟨a⁻¹, g⁻¹, by rw [smul_comm a⁻¹ g⁻¹, inv_smul_smul, inv_smul_smul]⟩
          trans := by
            rintro d d' d'' ⟨a, g, rfl⟩ ⟨a', g', rfl⟩
            exact ⟨a * a', g * g', by rw [mul_smul, mul_smul, smul_comm g a' (g' • d'')]⟩ } }
  let o : S.D → S.D := fun d => Quotient.out (Quotient.mk r d)
  have ho : ∀ d, ∃ (a : A) (g : S.G), a • g • d = o d := fun d => Quotient.exact (Quotient.out_eq (Quotient.mk r d))
  have hog : ∀ (g : S.G) d, o (g • d) = o d := by
    intro g d
    have : Quotient.mk r (g • d) = Quotient.mk r d := Quotient.sound ⟨1, g, by rw [one_smul]⟩
    show Quotient.out (Quotient.mk r (g • d)) = _
    rw [this]
  have hoa : ∀ (a : A) d, o (a • d) = o d := by
    intro a d
    have : Quotient.mk r (a • d) = Quotient.mk r d := Quotient.sound ⟨a, 1, by rw [one_smul]⟩
    show Quotient.out (Quotient.mk r (a • d)) = _
    rw [this]
  refine ⟨⟨{ carrier := {d | S.cls d = S.cls (o d)}, smul_mem' := ?_ }, ?_⟩⟩
  · intro g d hd
    show S.cls (g • d) = S.cls (o (g • d))
    rw [hog, S.cls_smul]
    exact hd
  · intro d
    obtain ⟨a, g, hag⟩ := ho d
    refine ⟨a, ?_, ?_⟩
    · show S.cls (a • d) = S.cls (o (a • d))
      rw [hoa, ← hag, smul_comm, S.cls_smul]
    · intro b hb
      have hb' : S.cls (b • d) = S.cls (o (b • d)) := hb
      have ha' : S.cls (a • d) = S.cls (o d) := by rw [← hag, smul_comm, S.cls_smul]
      rw [hoa, ← ha'] at hb'
      have h1 : (b * a⁻¹) • (a • d) = b • d := by rw [mul_smul, inv_smul_smul]
      rw [← h1] at hb'
      have h2 := hf _ _ hb'
      exact mul_inv_eq_one.mp h2

namespace Slice

variable {S A} (σ : S.Slice A)

def a (d : S.D) : A := (σ.uniq d).choose

theorem a_mem (d : S.D) : σ.a d • d ∈ σ.T := by
  exact (σ.uniq d).choose_spec.1

theorem a_eq {d : S.D} {b : A} (hb : b • d ∈ σ.T) : σ.a d = b := by
  exact ((σ.uniq d).choose_spec.2 b hb).symm

def glue (F : A → (S.restr σ.T).EqFun) (d : S.D) : S.V :=
  ((F (σ.a d)⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨σ.a d • d, σ.a_mem d⟩

theorem glue_eq (F : A → (S.restr σ.T).EqFun) (d : S.D) (b : A) (hb : b • d ∈ σ.T) :
    σ.glue F d = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
  have e := σ.a_eq hb
  have aux : ∀ (c : A) (_ : b = c) (t' : σ.T) (_ : (t' : S.D) = b • d),
      ((F c⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
    rintro _ rfl t' ht
    obtain rfl : t' = ⟨b • d, hb⟩ := Subtype.ext ht
    rfl
  exact aux _ e.symm _ (show σ.a d • d = b • d by rw [e])

variable [SMulCommClass A S.G S.D]

def split : S.EqFun ≃ₗ[K] (A → (S.restr σ.T).EqFun) where
  toFun φ b := ⟨fun t => (φ : S.D → S.V) (b • ((t : σ.T) : S.D)), fun (g : S.G) t => by
    show (φ : S.D → S.V) (b • g • ((t : σ.T) : S.D)) = S.ρ g ((φ : S.D → S.V) (b • ((t : σ.T) : S.D)))
    rw [smul_comm, φ.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨σ.glue F, fun g d => by
    have hb : σ.a d • g • d ∈ σ.T := by
      rw [smul_comm]
      exact σ.T.smul_mem g (σ.a_mem d)
    rw [σ.glue_eq F (g • d) (σ.a d) hb]
    have h1 := (F (σ.a d)⁻¹).2 g ⟨σ.a d • d, σ.a_mem d⟩
    have h2 : (⟨σ.a d • g • d, hb⟩ : σ.T) = g • (⟨σ.a d • d, σ.a_mem d⟩ : σ.T) :=
      Subtype.ext (smul_comm _ _ _)
    rw [h2]
    exact h1⟩
  left_inv φ := by
    apply Subtype.ext
    funext d
    show (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) = (φ : S.D → S.V) d
    rw [inv_smul_smul]
  right_inv F := by
    funext b
    apply Subtype.ext
    funext t
    have hb : b⁻¹ • b • ((t : σ.T) : S.D) ∈ σ.T := by
      rw [inv_smul_smul]
      exact (t : σ.T).2
    show σ.glue F (b • ((t : σ.T) : S.D)) = _
    rw [σ.glue_eq F _ b⁻¹ hb]
    have aux : ∀ (c : A) (_ : c = b) (t' : σ.T) (_ : t' = t),
        ((F c : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b : (S.restr σ.T).EqFun) : σ.T → S.V) t := by
      rintro _ rfl _ rfl
      rfl
    exact aux _ (inv_inv b) _ (Subtype.ext (inv_smul_smul _ _))

theorem split_apply (φ : S.EqFun) (b : A) (t : σ.T) :
    ((σ.split φ b : (S.restr σ.T).EqFun) : σ.T → S.V) t = (φ : S.D → S.V) (b • (t : S.D)) := rfl

def dia (S : GSD K) {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D] (b : A) : LocOp S S :=
  LocOp.ofMap (MonoidHom.id S.G) (fun d => b • d) LinearMap.id (fun g d => smul_comm b g d) (fun _ _ => rfl)

theorem dia_apply (b : A) (φ : S.EqFun) (d : S.D) :
    (((dia S b).op φ : S.EqFun) : S.D → S.V) d = (φ : S.D → S.V) (b • d) := by
  show (Finsupp.single (b • d) (LinearMap.id : S.V →ₗ[K] S.V)).sum (fun d k => k ((φ : S.D → S.V) d)) = _
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

theorem split_dia (b c : A) (φ : S.EqFun) : σ.split ((dia S b).op φ) c = σ.split φ (b * c) := by
  apply Subtype.ext
  funext t
  show (((dia S b).op φ : S.EqFun) : S.D → S.V) (c • (t : S.D)) = (φ : S.D → S.V) ((b * c) • (t : S.D))
  rw [dia_apply, mul_smul]

theorem split_mem_intOf (N : S.D → Submodule (𝓞 K) S.V) (hN : ∀ (b : A) (d : S.D), N (b • d) = N d) (φ : S.EqFun) :
    φ ∈ S.intOf N ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intOf (fun t => N ((t : σ.T) : S.D)) := by
  constructor
  · intro hφ b t
    show (φ : S.D → S.V) (b • (t : S.D)) ∈ N (t : S.D)
    rw [← hN b]
    exact hφ _
  · intro H d
    have h1 : (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) ∈ N (σ.a d • d) := H (σ.a d)⁻¹ ⟨σ.a d • d, σ.a_mem d⟩
    rw [inv_smul_smul, hN] at h1
    exact h1

theorem split_mem_intNab (hN : ∀ (b : A) (d : S.D), S.Nab (b • d) = S.Nab d) (φ : S.EqFun) :
    φ ∈ S.intNab ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intNab := by
  exact σ.split_mem_intOf S.Nab hN φ

theorem split_mem_intDel (hN : ∀ (b : A) (d : S.D), S.Del (b • d) = S.Del d) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intDel := by
  exact σ.split_mem_intOf S.Del hN φ

theorem card_stab_smul' (b : A) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (b • d)) = Nat.card (MulAction.stabilizer S.G d) := by
  have hs : MulAction.stabilizer S.G (b • d) = MulAction.stabilizer S.G d := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← smul_comm b g d, smul_left_cancel_iff]
  rw [hs]

def clEquiv (sT : (S.restr σ.T).Sec) : A × (S.restr σ.T).Cl ≃ S.Cl :=
  Equiv.ofBijective (fun p => S.cls (p.1 • ((sT.rep p.2 : σ.T) : S.D))) (by
    have := SMulCommClass.symm A S.G S.D
    constructor
    · rintro ⟨b, c⟩ ⟨b', c'⟩ hp
      obtain ⟨g, hg⟩ := (S.cls_eq_iff _ _).mp hp
      have hg' : g • b' • ((sT.rep c' : σ.T) : S.D) = b • ((sT.rep c : σ.T) : S.D) := hg
      have h1 : (b⁻¹ * b') • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [mul_smul, smul_comm b' g, hg', inv_smul_smul]
        exact (sT.rep c : σ.T).2
      have h2 : (1 : A) • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [one_smul]
        exact σ.T.smul_mem g (sT.rep c' : σ.T).2
      have h3 : b⁻¹ * b' = 1 := (σ.a_eq h1).symm.trans (σ.a_eq h2)
      have h4 : b' = b := (inv_mul_eq_one.mp h3).symm
      subst h4
      rw [smul_comm] at hg'
      have h5 := MulAction.injective b' hg'
      have h6 : (S.restr σ.T).cls (sT.rep c) = (S.restr σ.T).cls (sT.rep c') :=
        (S.restr_cls_eq_iff σ.T _ _).mpr ((S.cls_eq_iff _ _).mpr ⟨g, h5⟩)
      rw [sT.spec, sT.spec] at h6
      rw [h6]
    · intro c
      obtain ⟨d, rfl⟩ : ∃ d, S.cls d = c := ⟨Quotient.out c, Quotient.out_eq c⟩
      let t : σ.T := ⟨σ.a d • d, σ.a_mem d⟩
      refine ⟨((σ.a d)⁻¹, (S.restr σ.T).cls t), ?_⟩
      obtain ⟨g, hg⟩ : ∃ g : S.G, g • (sT.rep ((S.restr σ.T).cls t) : σ.T) = t := sT.exists_mv t
      have hg' : g • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D) = σ.a d • d := congrArg Subtype.val hg
      show S.cls ((σ.a d)⁻¹ • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D)) = S.cls d
      rw [← S.cls_smul g, smul_comm, hg', inv_smul_smul])

def sec (sT : (S.restr σ.T).Sec) : S.Sec where
  rep := fun c => ((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D)
  spec := fun c => (σ.clEquiv sT).apply_symm_apply c

theorem ipOf_split [Fintype A] (h : S.Ok) (s : S.Sec) (sT : (S.restr σ.T).Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = ∑ b : A, (S.restr σ.T).ipOf (S.restr_ok h σ.T) sT (σ.split φ b) (σ.split ψ b) := by
  let _ := h.fintypeCl
  let _ := (S.restr_ok h σ.T).fintypeCl
  rw [S.ipOf_indep h s (σ.sec sT), GSD.ipOf_eq_sum]
  simp only [GSD.ipOf_eq_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (σ.clEquiv sT).symm _ _ fun c => ?_
  show ((Nat.card (MulAction.stabilizer S.G
      (((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D))) : K))⁻¹ * _ = _
  rw [card_stab_smul', ← S.restr_card_stab σ.T]
  rfl

end Slice

end GSD

section Fib

variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)

def fibre (x : D₀) : SubMulAction (MulAction.stabilizer G x) D where
  carrier := {d | pr d = x}
  smul_mem' := by
    intro γ d hd
    show pr ((γ : G) • d) = x
    rw [hpr, show pr d = x from hd]
    exact γ.2

def orbitsFib (rep : MulAction.orbitRel.Quotient G D₀ → D₀)
    (hrep : ∀ c, (Quotient.mk'' (rep c) : MulAction.orbitRel.Quotient G D₀) = c) :
    (Σ c : MulAction.orbitRel.Quotient G D₀,
      MulAction.orbitRel.Quotient (MulAction.stabilizer G (rep c)) (fibre pr hpr (rep c))) ≃
      MulAction.orbitRel.Quotient G D :=
  Equiv.ofBijective
    (fun p => Quotient.map' (s₂ := MulAction.orbitRel G D) (fun y : fibre pr hpr (rep p.1) => (y : D))
      (by
        rintro y y' ⟨γ, hγ⟩
        exact ⟨(γ : G), congrArg Subtype.val hγ⟩) p.2)
    (by
      constructor
      · rintro ⟨c, q⟩ ⟨c', q'⟩ h
        induction q using Quotient.inductionOn' with
        | h y =>
        induction q' using Quotient.inductionOn' with
        | h y' =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • (y' : D) = (y : D) := Quotient.exact' h
        have h1 : g • rep c' = rep c := by
          rw [← show pr (y' : D) = rep c' from y'.2, ← hpr, hg]
          exact y.2
        have hc : c = c' := by
          rw [← hrep c, ← hrep c']
          exact Quotient.sound' ⟨g, h1⟩
        subst hc
        refine congrArg (Sigma.mk c) (Quotient.sound' ⟨⟨g, h1⟩, Subtype.ext hg⟩)
      · intro q
        induction q using Quotient.inductionOn' with
        | h d =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • pr d = rep (Quotient.mk'' (pr d)) := Quotient.exact' (hrep (Quotient.mk'' (pr d)))
        refine ⟨⟨Quotient.mk'' (pr d), Quotient.mk'' ⟨g • d, (hpr g d).trans hg⟩⟩, ?_⟩
        exact Quotient.sound' ⟨g, rfl⟩)

theorem fibre_card_stab (x : D₀) (y : fibre pr hpr x) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G x) y) = Nat.card (MulAction.stabilizer G (y : D)) := by
  have h1 : ∀ γ : MulAction.stabilizer (MulAction.stabilizer G x) y,
      ((γ : MulAction.stabilizer G x) : G) ∈ MulAction.stabilizer G (y : D) := fun γ =>
    MulAction.mem_stabilizer_iff.mpr (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp γ.2))
  have hy : pr (y : D) = x := y.2
  have h2 : ∀ g : MulAction.stabilizer G (y : D), (g : G) ∈ MulAction.stabilizer G x := by
    intro g
    have hg : (g : G) • (y : D) = y := MulAction.mem_stabilizer_iff.mp g.2
    refine MulAction.mem_stabilizer_iff.mpr ?_
    calc (g : G) • x = (g : G) • pr (y : D) := by rw [hy]
      _ = pr ((g : G) • (y : D)) := (hpr _ _).symm
      _ = pr (y : D) := by rw [hg]
      _ = x := hy
  have h3 : ∀ g : MulAction.stabilizer G (y : D),
      (⟨(g : G), h2 g⟩ : MulAction.stabilizer G x) ∈ MulAction.stabilizer (MulAction.stabilizer G x) y := fun g =>
    MulAction.mem_stabilizer_iff.mpr (Subtype.ext (MulAction.mem_stabilizer_iff.mp g.2))
  exact Nat.card_congr ⟨fun γ => ⟨_, h1 γ⟩, fun g => ⟨_, h3 g⟩, fun γ => rfl, fun g => rfl⟩

end Fib

theorem GSD.triv_point_ip (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G]
    (h : (GSD.triv K G PUnit).Ok) :
    (GSD.triv K G PUnit).ip h (GSD.trivOne K G PUnit) (GSD.trivOne K G PUnit) = ((Nat.card G : K))⁻¹ := by
  let _ := h.fintypeCl
  unfold GSD.ip
  rw [GSD.ipOf_eq_sum]
  have hs : Subsingleton (GSD.triv K G PUnit).Cl := by
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn' with
    | h x =>
    induction b using Quotient.inductionOn' with
    | h y => rfl
  rw [Fintype.sum_subsingleton _ ((GSD.triv K G PUnit).cls PUnit.unit)]
  have h2 : ∀ x : PUnit, Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    intro x
    have h1 : MulAction.stabilizer G x = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rfl
    rw [h1]
    exact Subgroup.card_top
  have h3 := h2 ((GSD.triv K G PUnit).outSec.rep ((GSD.triv K G PUnit).cls PUnit.unit))
  refine Eq.trans (congrArg (fun n : ℕ => ((n : K))⁻¹ * _) h3) ?_
  show ((Nat.card G : K))⁻¹ * (star (1 : K) * 1) = _
  simp

theorem LocOp.op_mem_intOf {S S' : GSD K} (A : LocOp S S') (N : S.D → Submodule (𝓞 K) S.V)
    (N' : S'.D → Submodule (𝓞 K) S'.V) (hk : ∀ d' d, ∀ x ∈ N d, A.ker d' d x ∈ N' d') (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : A.op φ ∈ S'.intOf N' := by
  intro d'
  show ∑ d ∈ (A.ker d').support, (A.ker d' d) ((φ : S.D → S.V) d) ∈ N' d'
  exact sum_mem fun d _ => hk d' d _ (hφ d)

theorem ClsKer.opOf_mem_intOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (n : ℕ) (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : (n : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by
  intro d'
  show (n : 𝓞 K) • A.appOf h s φ d' ∈ N' d'
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨m, hm⟩ := hn c
  have hw : (((S.toCSDOf h s).wt c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by unfold CSD.wt; exact @Fintype.card_ne_zero _ ((S.toCSDOf h s).finGam c) ⟨1⟩)
  have e1 : ((n : 𝓞 K) • ((((S.toCSDOf h s).wt c : ℕ) : K))⁻¹) = ((m : ℕ) : K) := by
    rw [Algebra.smul_def, map_natCast, hm, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rw [← smul_assoc, e1, Nat.cast_smul_eq_nsmul]
  exact (N' d').nsmul_mem (hk _ d' _ (hφ _)) m

theorem ClsKer.opOf_mem_intOf_DGam {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (φ : S.EqFun) (hφ : φ ∈ S.intOf N) :
    ((S.toCSDOf h s).DGam : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by
  letI := h.fintypeCl
  exact A.opOf_mem_intOf h s N N' hk _ (fun c => by unfold CSD.DGam; exact Finset.dvd_lcm (Finset.mem_univ c)) φ hφ

namespace GSD

variable (S : GSD K)

theorem csOf_indep (h : S.Ok) (s s' : S.Sec) {M : Type} [AddCommGroup M] [Module K M] (F : S.D → M)
    (hF : ∀ (g : S.G) (d : S.D), F (g • d) = F d) : S.csOf h s F = S.csOf h s' F := by
  unfold csOf
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [S.wt_eq h s c, S.wt_eq h s' c, ← hg, S.card_stab_smul, hF]

theorem ipOf_eq_csOf (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = S.csOf h s fun d => S.pair (φ d) (ψ d) := rfl

theorem csOf_mem (h : S.Ok) (s : S.Sec) {M : Type} [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (N : Submodule (𝓞 K) M) (F : S.D → M) (hF : ∀ d, F d ∈ N) (n : ℕ)
    (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) : (n : 𝓞 K) • S.csOf h s F ∈ N := by
  unfold csOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨m, hm⟩ := hn c
  have hw : (((S.toCSDOf h s).wt c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by unfold CSD.wt; exact @Fintype.card_ne_zero _ ((S.toCSDOf h s).finGam c) ⟨1⟩)
  have e1 : ((n : 𝓞 K) • ((((S.toCSDOf h s).wt c : ℕ) : K))⁻¹) = ((m : ℕ) : K) := by
    rw [Algebra.smul_def, map_natCast, hm, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rw [← smul_assoc, e1, Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem (hF _) m

end GSD

theorem ClsKer.appOf_eq_csOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (φ : S.D → S.V) (d' : S'.D) :
    A.appOf h s φ d' = S.csOf h s fun d => A.k d d' (φ d) := rfl

namespace BiPair

variable {S S' : GSD K} (P : BiPair S S')

theorem term_smul (φ : S.EqFun) (ψ : S'.EqFun) (g : S'.G) (d' : S'.D) :
    P.B ((φ : S.D → S.V) (P.p (g • d'))) ((ψ : S'.D → S'.V) (g • d')) =
      P.B ((φ : S.D → S.V) (P.p d')) ((ψ : S'.D → S'.V) d') := by
  rw [P.hp, φ.2, ψ.2, P.inv]

theorem sumOf_indep (h' : S'.Ok) (s s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.sumOf h' s φ ψ = P.sumOf h' s' φ ψ := by
  unfold sumOf
  exact S'.csOf_indep h' s s' _ (fun g d' => P.term_smul φ ψ g d')

theorem formOf_apply (h' : S'.Ok) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.formOf h' s' φ ψ = P.sumOf h' s' φ ψ := rfl

theorem sumOf_mem (h' : S'.Ok) (s' : S'.Sec) (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hB : ∀ d', ∀ x ∈ N (P.p d'), ∀ y ∈ N' d', P.B x y ∈ (1 : Submodule (𝓞 K) K)) (n : ℕ)
    (hn : ∀ c, (S'.toCSDOf h' s').wt c ∣ n) (φ : S.EqFun) (hφ : φ ∈ S.intOf N) (ψ : S'.EqFun)
    (hψ : ψ ∈ S'.intOf N') : (n : 𝓞 K) • P.sumOf h' s' φ ψ ∈ (1 : Submodule (𝓞 K) K) := by
  unfold sumOf
  exact S'.csOf_mem h' s' 1 _ (fun d' => hB d' _ (hφ (P.p d')) _ (hψ d')) n hn

end BiPair

namespace GFam

variable (F : GFam K)

theorem wt_eq (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (c : F.Cl) :
    (F.toCSDOf h s).wt c = ((F.mem c.1).toCSDOf (h c.1) (s c.1)).wt c.2 := rfl

theorem ipOf_eq_csum (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) :
    F.ipOf h s φ ψ = (F.toCSDOf h s).csum (F.resOf h s φ).1 (F.resOf h s ψ).1 := by
  letI : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  unfold ipOf CSD.csum
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

theorem ipOf_indep (h : F.Ok) (s s' : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) : F.ipOf h s φ ψ = F.ipOf h s' φ ψ := by
  unfold ipOf
  exact Finset.sum_congr rfl fun b _ => (F.mem b).ipOf_indep (h b) (s b) (s' b) (φ b) (ψ b)

theorem mem_intNab (φ : F.Forms) : φ ∈ F.intNab ↔ ∀ b, φ b ∈ (F.mem b).intNab := by
  unfold intNab
  rw [Submodule.mem_pi]
  exact ⟨fun H b => H b (Set.mem_univ b), fun H b _ => H b⟩

theorem mem_intDel (φ : F.Forms) : φ ∈ F.intDel ↔ ∀ b, φ b ∈ (F.mem b).intDel := by
  unfold intDel
  rw [Submodule.mem_pi]
  exact ⟨fun H b => H b (Set.mem_univ b), fun H b _ => H b⟩

def coordOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) : F.Forms ≃ₗ[K] (Fin (F.toCSDOf h s).dim → K) :=
  (F.resOf h s).trans (F.toCSDOf h s).basis.equivFun

theorem I_coordOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    (F.toCSDOf h s).I (F.coordOf h s φ) = (F.resOf h s φ).1 := by
  show (((F.toCSDOf h s).basis.equivFun.symm ((F.toCSDOf h s).basis.equivFun (F.resOf h s φ)) :
    (F.toCSDOf h s).Forms) : F.Cl → F.V) = _
  rw [LinearEquiv.symm_apply_apply]

theorem coordOf_mem_nabLat (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    F.coordOf h s φ ∈ (F.toCSDOf h s).nabLat ↔ φ ∈ F.intNab := by
  unfold CSD.nabLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, F.I_coordOf h s φ, Submodule.mem_pi, F.mem_intNab]
  simp only [Set.mem_univ, true_implies, Sigma.forall]
  exact forall_congr' fun b => ((F.mem b).mem_intNab_iff (h b) (s b) (φ b)).symm

theorem coordOf_mem_delLat (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    F.coordOf h s φ ∈ (F.toCSDOf h s).delLat ↔ φ ∈ F.intDel := by
  unfold CSD.delLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, F.I_coordOf h s φ, Submodule.mem_pi, F.mem_intDel]
  simp only [Set.mem_univ, true_implies, Sigma.forall]
  exact forall_congr' fun b => ((F.mem b).mem_intDel_iff (h b) (s b) (φ b)).symm

theorem ipOf_coord (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) :
    F.ipOf h s φ ψ = hform (F.toCSDOf h s).H (F.coordOf h s φ) (F.coordOf h s ψ) := by
  rw [F.ipOf_eq_csum h s, ← F.I_coordOf h s φ, ← F.I_coordOf h s ψ, (F.toCSDOf h s).csum_sum]
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dim_eq_sum (h : F.Ok) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf h s).dim = ∑ b, finrank K (F.mem b).EqFun := by
  unfold CSD.dim
  haveI : ∀ b, Module.Finite K (F.mem b).EqFun := fun b => (F.mem b).finiteDimensional_EqFun (h b)
  rw [← (F.resOf h s).finrank_eq, Module.finrank_pi_fintype]

def Good (n : ℕ) : Prop := ∀ b, (F.mem b).Good n

theorem toCSDOf_good {n : ℕ} [Nonempty F.β] (G : F.Good n) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf (fun b => (G b).ok) s).Good n where
  symm := (G (Classical.arbitrary F.β)).symm
  nondeg := (G (Classical.arbitrary F.β)).nondeg
  inv := fun c γ x y => ((F.mem c.1).toCSDOf_good (G c.1) (s c.1)).inv c.2 γ x y
  nab_lat := fun c => (G c.1).nab_lat _
  del_le := fun c => (G c.1).del_le _
  del_stable := fun c γ y hy => ((F.mem c.1).toCSDOf_good (G c.1) (s c.1)).del_stable c.2 γ y hy
  s_pos := (G (Classical.arbitrary F.β)).s_pos
  dual_le := fun c => (G c.1).dual_le _
  del_dual := fun c => (G c.1).del_dual _

theorem toCSDOf_rat [Nonempty F.β] (h : F.Ok) (R : ∀ b, (F.mem b).Rat) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf h s).Rat where
  pair_rat := (R (Classical.arbitrary F.β)).pair_rat
  act_rat := fun c γ i j => (R c.1).act_rat (γ : F.G c.1) i j
  pos := (R (Classical.arbitrary F.β)).pos

theorem Mat.opOf_apply {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms)
    (b' : F'.β) : M.opOf h s φ b' = ∑ b, (M b b').opOf (h b) (s b) (φ b) := by
  simp only [Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem Mat.opOf_indep {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s s' : ∀ b, (F.mem b).Sec) :
    M.opOf h s = M.opOf h s' := by
  refine LinearMap.ext fun φ => funext fun b' => ?_
  rw [M.opOf_apply h s, M.opOf_apply h s']
  exact Finset.sum_congr rfl fun b _ => by rw [(M b b').opOf_indep (h b) (s b) (s' b)]

theorem Mat.resOf_opOf {F F' : GFam K} (M : Mat F F') (h : F.Ok) (h' : F'.Ok) (s : ∀ b, (F.mem b).Sec)
    (s' : ∀ b', (F'.mem b').Sec) (φ : F.Forms) :
    (F'.resOf h' s' (M.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((F.toCSDOf h s).wt c : K))⁻¹) (M.atReps s s') (F.resOf h s φ).1 := by
  funext c'
  letI : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  show ((M.opOf h s φ c'.1 : (F'.mem c'.1).EqFun) : (F'.mem c'.1).D → F'.V) ((s' c'.1).rep c'.2) = _
  rw [M.opOf_apply h s φ c'.1, Submodule.coe_sum, Finset.sum_apply]
  simp only [Formalism.ThetaLiftIndependence.kerOpM]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

end GFam

namespace GSD

variable (K)

def twSgn : ℤˣ →* Module.End K K where
  toFun g := (((g : ℤ) : K)) • (1 : Module.End K K)
  map_one' := by simp
  map_mul' a b := by
    ext
    simp [mul_comm]

theorem twSgn_apply (g : ℤˣ) (x : K) : twSgn K g x = ((g : ℤ) : K) * x := by
  show (((g : ℤ) : K) • (1 : Module.End K K)) x = ((g : ℤ) : K) * x
  rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]

abbrev tw : GSD K where
  G := ℤˣ
  D := Option ℤˣ
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := CSD.pairOne K
  ρ := twSgn K
  Nab := fun _ => 1
  Del := fun _ => 1

theorem map_twSgn (g : ℤˣ) :
    (1 : Submodule (𝓞 K) K) = (1 : Submodule (𝓞 K) K).map ((twSgn K g).restrictScalars (𝓞 K)) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, twSgn_apply]
  constructor
  · intro hx
    refine ⟨((g : ℤ) : K) * x, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
      exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K) * y, by simp⟩
    · rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hy
    exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K) * z, by simp⟩

theorem tw_ok : (tw K).Ok where
  fin_orb := by
    show Finite (MulAction.orbitRel.Quotient ℤˣ (Option ℤˣ))
    exact Quotient.finite _
  fin_stab := by
    intro d
    show Finite (MulAction.stabilizer ℤˣ (d : Option ℤˣ))
    infer_instance
  nab_smul := fun g _ => map_twSgn K g
  del_smul := fun g _ => map_twSgn K g
  inv := by
    intro g x y
    show CSD.pairOne K (twSgn K g x) (twSgn K g y) = CSD.pairOne K x y
    rw [CSD.pairOne_apply, CSD.pairOne_apply]
    erw [twSgn_apply, twSgn_apply]
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp

theorem tw_none (φ : (tw K).EqFun) : (φ.1 : Option ℤˣ → K) none = 0 := by
  have h2 : (φ.1 : Option ℤˣ → K) none = -(φ.1 : Option ℤˣ → K) none := by
    have h1 := φ.2 (-1) none
    rw [twSgn_apply] at h1
    convert h1 using 1 <;> first | rfl | simp
  have h3 : (2 : K) * (φ.1 : Option ℤˣ → K) none = 0 := by
    rw [two_mul]
    nth_rewrite 2 [h2]
    exact add_neg_cancel _
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

def twForm : (tw K).EqFun := ⟨fun d => match d with
    | none => (0 : K)
    | some g => ((g : ℤ) : K), by
  intro g d
  cases d with
  | none =>
    show (0 : K) = twSgn K g 0
    simp
  | some e =>
    show (((g * e : ℤˣ) : ℤ) : K) = twSgn K g ((e : ℤ) : K)
    rw [twSgn_apply]
    simp⟩

theorem twForm_mem : twForm K ∈ (tw K).intDel := by
  intro d
  cases d with
  | none => exact zero_mem _
  | some g => exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K), map_intCast _ _⟩

def twEquiv : (tw K).EqFun ≃ₗ[K] K where
  toFun φ := (φ.1 : Option ℤˣ → K) (some 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := a • twForm K
  left_inv φ := by
    apply Subtype.ext
    funext d
    cases d with
    | none =>
      show (φ.1 : Option ℤˣ → K) (some 1) * 0 = (φ.1 : Option ℤˣ → K) none
      rw [tw_none, mul_zero]
    | some e =>
      show (φ.1 : Option ℤˣ → K) (some 1) * ((e : ℤ) : K) = (φ.1 : Option ℤˣ → K) (some e)
      have h := φ.2 e (some (1 : ℤˣ) : Option ℤˣ)
      have h1 : (φ.1 : Option ℤˣ → K) (some (e * 1)) = twSgn K e ((φ.1 : Option ℤˣ → K) (some 1)) := h
      rw [mul_one, twSgn_apply] at h1
      rw [h1, mul_comm]
  right_inv a := by
    show a * (((1 : ℤˣ) : ℤ) : K) = a
    simp

theorem tw_finrank : finrank K (tw K).EqFun = 1 := by
  exact (twEquiv K).finrank_eq.trans (Module.finrank_self K)

theorem tw_dim : ((tw K).toCSD (tw_ok K)).dim = 1 := by
  exact ((tw K).finrank_EqFun (tw_ok K) (tw K).outSec).symm.trans (tw_finrank K)

theorem triv_rat (G D : Type) [Group G] [MulAction G D] : (GSD.triv K G D).Rat where
  pair_rat := by
    intro (i : Unit) (j : Unit)
    show CSD.pairOne K ((Basis.singleton Unit K) i) ((Basis.singleton Unit K) j) ∈ cmMax K
    rw [CSD.pairOne_apply, Basis.singleton_apply, star_one, one_mul]
    exact (cmMax K).one_mem
  act_rat := by
    intro g (i : Unit) (j : Unit)
    show (Basis.singleton Unit K).repr ((1 : Module.End K K) ((Basis.singleton Unit K) j)) i ∈ cmMax K
    rw [Module.End.one_apply, Basis.repr_self]
    cases i; cases j
    simp
  pos := by
    intro v
    have : ((GSD.triv K G D).gramV.map v.embedding) = (1 : Matrix Unit Unit ℂ) := by
      ext (i : Unit) (j : Unit)
      show v.embedding (CSD.pairOne K ((Basis.singleton Unit K) i) ((Basis.singleton Unit K) j)) = _
      rw [CSD.pairOne_apply, Basis.singleton_apply, star_one, one_mul, map_one]
      rfl
    rw [this]
    exact Matrix.PosDef.one

abbrev tv : GSD K := GSD.triv K ℤˣ (Option ℤˣ)

theorem tv_ok : (tv K).Ok := by
  refine ⟨inferInstance, fun _ => inferInstance, fun g _ => ?_, fun g _ => ?_, fun g x y => rfl⟩
  · rw [MonoidHom.one_apply]
    exact (Submodule.map_id _).symm
  · rw [MonoidHom.one_apply]
    exact (Submodule.map_id _).symm

def isS : (tv K).Cl → Bool := Quotient.lift Option.isSome (by
  rintro a b ⟨g, rfl⟩
  cases b <;> rfl)

def eCl : (tv K).Cl ≃ Bool := Equiv.ofBijective (isS K) ⟨by
  rintro ⟨a⟩ ⟨b⟩ h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => exact absurd h (by simp [isS])
  | some x =>
    cases b with
    | none => exact absurd h (by simp [isS])
    | some y =>
      refine Quotient.sound ⟨x * y⁻¹, ?_⟩
      show some ((x * y⁻¹) * y) = some x
      rw [inv_mul_cancel_right], by
  intro b
  cases b
  · exact ⟨(tv K).cls none, rfl⟩
  · exact ⟨(tv K).cls (some 1), rfl⟩⟩

theorem card_rep (s : (tv K).Sec) (d : Option ℤˣ) :
    Nat.card (MulAction.stabilizer ℤˣ (s.rep ((tv K).cls d))) = Nat.card (MulAction.stabilizer ℤˣ d) := by
  obtain ⟨g, hg⟩ := ((tv K).cls_eq_iff _ _).mp (s.spec ((tv K).cls d))
  rw [← hg]
  exact (tv K).card_stab_smul g d

theorem card_none : Nat.card (MulAction.stabilizer ℤˣ (none : Option ℤˣ)) = 2 := by
  rw [show MulAction.stabilizer ℤˣ (none : Option ℤˣ) = ⊤ from (Subgroup.eq_top_iff' _).mpr fun g => rfl,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  first | rfl | decide | simp

theorem card_some : Nat.card (MulAction.stabilizer ℤˣ (some 1 : Option ℤˣ)) = 1 := by
  have hb : MulAction.stabilizer ℤˣ (some 1 : Option ℤˣ) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    have h1 : (some (g • (1 : ℤˣ)) : Option ℤˣ) = some 1 := hg
    simpa using h1
  rw [hb, Subgroup.card_bot]

theorem triv_mass : (tv K).ip (tv_ok K) (fun _ => (1 : K)) (fun _ => (1 : K)) = 3 / 2 := by
  unfold GSD.ip
  rw [GSD.ipOf_eq_sum]
  let _ := (tv_ok K).fintypeCl
  rw [← (eCl K).symm.sum_comp, Fintype.sum_bool]
  have e1 : (eCl K).symm true = (tv K).cls (some 1) := (eCl K).symm_apply_eq.mpr rfl
  have e0 : (eCl K).symm false = (tv K).cls none := (eCl K).symm_apply_eq.mpr rfl
  rw [e1, e0, card_rep, card_rep, card_none, card_some, CSD.pairOne_apply]
  norm_num

theorem stab_inj {Γ H D : Type} [Group Γ] [Group H] [MulAction (Γ × H) D]
    (free : ∀ (h : H) (d : D), ((1, h) : Γ × H) • d = d → h = 1) (d : D) :
    Function.Injective (fun x : MulAction.stabilizer (Γ × H) d => (x : Γ × H).1) := by
  intro x y hxy
  have hxy' : (x : Γ × H).1 = (y : Γ × H).1 := hxy
  set z : Γ × H := (x : Γ × H)⁻¹ * (y : Γ × H) with hzdef
  have hz : z • d = d := by
    rw [hzdef, mul_smul, MulAction.mem_stabilizer_iff.mp y.2, inv_smul_eq_iff, MulAction.mem_stabilizer_iff.mp x.2]
  have h1 : z.1 = 1 := by
    rw [hzdef, Prod.fst_mul, Prod.fst_inv, ← hxy', inv_mul_cancel]
  have h3 : ((1, z.2) : Γ × H) = z := Prod.ext h1.symm rfl
  have h2 : z.2 = 1 := free z.2 d (by rw [h3]; exact hz)
  have h4 : z = 1 := Prod.ext h1 h2
  exact Subtype.ext (inv_mul_eq_one.mp h4)

end GSD

end Formalism.L2.Col
