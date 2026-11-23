import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem exists_equiv_of_map_eq {β : Type*} {h N : ℕ} (x : Fin h → β) (F : Fin N → β)
    (hx : (Finset.univ.val.map x : Multiset β) = Finset.univ.val.map F) :
    ∃ σ : Fin h ≃ Fin N, ∀ a, x a = F (σ a) := by
  have hcount : ∀ {M : ℕ} (f : Fin M → β) (c : β),
      Fintype.card {a // f a = c} = Multiset.count c (Finset.univ.val.map f) := by
    intro M f c
    rw [Multiset.count_map, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun a _ => eq_comm
  have hcard : ∀ c, Fintype.card {a // x a = c} = Fintype.card {b // F b = c} := fun c => by
    rw [hcount, hcount, hx]
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
    fun a => (Equiv.ofFiberEquiv_map _ a).symm⟩

theorem sum_map_univ {β : Type*} {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (f : ∀ a, Fin (d a) → β) (F : Fin N → β) (hF : ∀ a j, F (e ⟨a, j⟩) = f a j) :
    (∑ a, (Finset.univ.val.map (f a) : Multiset β)) = Finset.univ.val.map F := by
  have h1 : ∀ {ι : Type} [Fintype ι] (g : ι → β),
      (Finset.univ.val.map g : Multiset β) = ∑ i, ({g i} : Multiset β) := by
    intro ι _ g
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map g), Multiset.map_map]
    rfl
  rw [h1 F, ← Equiv.sum_comp e, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => by rw [hF]

theorem deltaHalf_inv_apply (g : Levi k fun a : Fin G.s => Fin (G.d a)) :
    ((((deltaHalf k fun a : Fin G.s => Fin (G.d a))⁻¹ g : ℂˣ)) : ℂ) =
      ∏ a, ((absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
        (GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, deltaHalf_apply, ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [absPow_neg]
  rfl

theorem piTensor_twD_eq {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) :
    piTensor (G.twD τ) = twist (piTensor τ) (deltaHalf k fun a : Fin G.s => Fin (G.d a))⁻¹ := by
  refine MonoidHom.ext fun g => ?_
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun x => ?_
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, twist_apply, Grp.twD, detChar_apply]
  rw [MultilinearMap.map_smul_univ, deltaHalf_inv_apply]

theorem isIrreducible_piTensor_twD (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {Y : Fin G.s → Type}
    [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a))
    (hs : ∀ a, IsSmooth (G.twD τ a)) (hi : ∀ a, (G.twD τ a).IsIrreducible) :
    (piTensor (G.twD τ)).IsIrreducible := by
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hi fun a => ?_
  exact GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (G.d a))) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO _ _ (hi a) ((hBZ k).1 (Fin (G.d a)) _ _ (hs a) (hi a))

theorem hasSupport_twD {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ)
    (hν : ∀ a j, IsSmoothChar (ν a j))
    (hc : ∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) (a : Fin G.s)
    (hsm : ∀ j, IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2)))) :
    HasSupport (G.twD τ a) (Finset.univ.val.map fun j => IrrGL.ofChar _ (hsm j)) := by
  have hψ : IsSmoothChar (absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    isSmoothChar_absPow _
  have h2 := (hasSupport_of_isCuspSupport (hc a)).tw _ hψ
  rw [Multiset.map_map] at h2
  have key : (Finset.univ.val.map fun j => IrrGL.ofChar _ (hsm j)) =
      Finset.univ.val.map ((fun y : IrrGL k => y.tw _ hψ) ∘ fun j =>
        IrrGL.of (detRep (Fin 1) (ν a j)) ((hc a).2.1 j).2.2.1 ((hc a).2.1 j).2.1) :=
    Multiset.map_congr rfl fun j _ => (IrrGL.tw_ofChar (ν a j) _ (hν a j) hψ).symm
  rw [key]
  exact h2

end P_spSupp

open P_spSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

theorem step_spSupp (G : Grp k n) : G.SpecialSupportProp := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _

  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm

  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy

  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])

  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2

end UpperTheory.TNZ.Grp
