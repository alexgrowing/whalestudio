import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulMemLatOf
import Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIDown

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

open Formalism.MainNotions.G

variable {W Qq F : Type} [CommRing W] [Field Qq] [Algebra W Qq] [Field F] [Algebra W F] {n : ℕ}
  [IsDomain W] [IsPrincipalIdealRing W] [IsFractionRing W Qq]

def gUp (p : ℕ) (g : Matrix (Fin n) (Fin n) Qq) : Matrix (Fin n) (Fin n) Qq := ((p : Qq))⁻¹ • g

theorem pQ_ne {p : ℕ} (h : Res (p : W) F) : (p : Qq) ≠ 0 := by
  rw [← map_natCast (algebraMap W Qq) p]
  exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr h.ne

theorem smul_psi_gUp {p : ℕ} (h : Res (p : W) F) (g : Matrix (Fin n) (Fin n) Qq) (w : Fin n → W) :
    (p : W) • psi (gUp p g) w = psi g w := by
  unfold gUp
  rw [psi_smul_mat, ← algebraMap_smul Qq (p : W), map_natCast, smul_smul,
    mul_inv_cancel₀ (pQ_ne (Qq := Qq) h), one_smul]

theorem gUp_det {p : ℕ} (h : Res (p : W) F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) :
    IsUnit (gUp p g).det := by
  unfold gUp
  rw [Matrix.det_smul]
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (pQ_ne (Qq := Qq) h))).pow _).mul hg

private theorem psi_injective_of_isUnit_det (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) :
    Function.Injective (psi (W := W) g) := by
  intro a b hab
  rw [psi_apply, psi_apply] at hab
  have hinj : Function.Injective g.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)
  funext c
  exact IsFractionRing.injective W Qq (congrFun (hinj hab) c)

theorem psi_gUp_mem {p : ℕ} (h : Res (p : W) F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    (w : Fin n → W) : psi (gUp p g) w ∈ colSpan W g ↔ red F n w = 0 := by
  constructor
  · intro hm
    obtain ⟨y, hy⟩ := (mem_colSpan (W := W) g _).1 hm
    refine (red_eq_zero h w).2 ⟨y, psi_injective_of_isUnit_det g hg ?_⟩
    rw [map_smul, ← smul_psi_gUp h g w, hy, ← psi_apply]
  · intro h0
    obtain ⟨w', rfl⟩ := (red_eq_zero h w).1 h0
    rw [map_smul, smul_psi_gUp h]
    exact (mem_colSpan (W := W) g _).2 ⟨w', psi_apply g w'⟩

theorem card_up {p : ℕ} (h : Res (p : W) F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    (U : Submodule F (Fin n → F)) :
    Nat.card (↥(LatOf (W := W) (gUp p g) U) ⧸ Submodule.comap (LatOf (W := W) (gUp p g) U).subtype (colSpan W g)) =
      Nat.card F ^ Module.finrank F U := by
  classical
  let M : Submodule W (Fin n → W) := Submodule.comap (red F n) (U.restrictScalars W)
  have inj : Function.Injective (psi (W := W) (gUp p g)) := psi_injective_of_isUnit_det _ (gUp_det h g hg)
  let e : M ≃ₗ[W] M.map (psi (gUp p g)) := Submodule.equivMapOfInjective _ inj M
  let f : M →ₗ[W] U.restrictScalars W := (red F n).restrict (fun x hx => hx)
  have hf : Function.Surjective f := by
    rintro ⟨u, hu⟩
    choose w hw using fun c => h.surj (u c)
    have hred : red F n w = u := funext fun c => by rw [red_apply, hw]
    refine ⟨⟨w, ?_⟩, ?_⟩
    · show red F n w ∈ U
      rw [hred]; exact hu
    · exact Subtype.ext hred
  have hQ : (LinearMap.ker f).map (e : M →ₗ[W] M.map (psi (gUp p g))) =
      Submodule.comap (M.map (psi (gUp p g))).subtype (colSpan W g) := by
    ext z
    obtain ⟨m, rfl⟩ := e.surjective z
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker, Submodule.mem_comap,
      Submodule.subtype_apply]
    have he : ((e m : M.map (psi (gUp p g))) : Fin n → Qq) = psi (gUp p g) (m : Fin n → W) := rfl
    rw [he, psi_gUp_mem h g hg]
    exact Subtype.ext_iff
  calc Nat.card (↥(LatOf (W := W) (gUp p g) U) ⧸
          Submodule.comap (LatOf (W := W) (gUp p g) U).subtype (colSpan W g))
        = Nat.card (M ⧸ LinearMap.ker f) :=
          Nat.card_congr (Submodule.Quotient.equiv _ _ e hQ).toEquiv.symm
    _ = Nat.card (U.restrictScalars W) := Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv
    _ = Nat.card U := rfl
    _ = Nat.card F ^ Module.finrank F U := Module.natCard_eq_pow_finrank

theorem edge_up_iff (p n' k : ℕ) (h : Res (p : W) F) (hq : Nat.card F = p ^ n') (hq1 : 2 ≤ p ^ n')
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (U : Submodule F (Fin n → F)) :
    IsEdge p n' k ⟨colSpan W g, LatOf (W := W) (gUp p g) U⟩ ↔ Module.finrank F U = k := by
  have hle : colSpan W g ≤ LatOf (W := W) (gUp p g) U := by
    intro y hy
    obtain ⟨w, rfl⟩ := (mem_colSpan (W := W) g y).1 hy
    rw [← psi_apply, ← smul_psi_gUp h g w, ← map_smul]
    refine (psi_mem_LatOf (gUp p g) (gUp_det h g hg) U _).2 ?_
    rw [(red_eq_zero h _).2 ⟨w, rfl⟩]
    exact U.zero_mem
  have hsm : ∀ x ∈ LatOf (W := W) (gUp p g) U, (p : W) • x ∈ colSpan W g := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Submodule.mem_map.1 hx
    rw [smul_psi_gUp h g w]
    exact (mem_colSpan (W := W) g _).2 ⟨w, psi_apply g w⟩
  have hcard : Nat.card (↥(LatOf (W := W) (gUp p g) U) ⧸
      Submodule.comap (LatOf (W := W) (gUp p g) U).subtype (colSpan W g)) =
        (p ^ n') ^ Module.finrank F U := by
    rw [card_up h g hg U, hq]
  unfold IsEdge
  dsimp only
  rw [hcard, pow_mul]
  constructor
  · rintro ⟨-, -, -, -, hc⟩
    exact Nat.pow_right_injective hq1 hc
  · intro hk
    exact ⟨⟨g, hg, rfl⟩, LatOf_lattice h (gUp p g) (gUp_det h g hg) U, hle, hsm, by rw [hk]⟩

theorem up_card (p n' k : ℕ) (h : Res (p : W) F) (hq : Nat.card F = p ^ n') (hq1 : 2 ≤ p ^ n')
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (Pd : Submodule W (Fin n → Qq) → Prop)
    (Pu : Submodule F (Fin n → F) → Prop) (hP : ∀ U, Pd (LatOf (W := W) (gUp p g) U) ↔ Pu U) :
    Nat.card {A1 : Submodule W (Fin n → Qq) // IsEdge p n' k ⟨colSpan W g, A1⟩ ∧ Pd A1} =
      Nat.card {U : Submodule F (Fin n → F) // Pu U ∧ Module.finrank F U = k} := by
  have hgu := gUp_det h g hg
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun U => ⟨LatOf (W := W) (gUp p g) U.1,
      (edge_up_iff p n' k h hq hq1 g hg U.1).2 U.2.2, (hP U.1).2 U.2.1⟩) ⟨?_, ?_⟩)
  · rintro ⟨U, hU⟩ ⟨U', hU'⟩ he
    exact Subtype.ext (LatOf_inj h (gUp p g) hgu (congrArg Subtype.val he))
  · rintro ⟨A1, hE, hPd⟩
    have hE' := hE
    unfold IsEdge at hE'
    dsimp only at hE'
    obtain ⟨-, -, hle, hsm, -⟩ := hE'
    have h1 : A1 ≤ colSpan W (gUp p g) := by
      intro x hx
      obtain ⟨w, hw⟩ := (mem_colSpan (W := W) g _).1 (hsm x hx)
      refine (mem_colSpan (W := W) (gUp p g) x).2 ⟨w, ?_⟩
      rw [← psi_apply]
      have hpx : (p : W) • x = (p : W) • psi (gUp p g) w := by
        rw [hw, smul_psi_gUp h g w, psi_apply]
      rw [← algebraMap_smul Qq (p : W) x, ← algebraMap_smul Qq (p : W), map_natCast] at hpx
      exact smul_right_injective (Fin n → Qq) (pQ_ne h) hpx
    have h2 : ∀ y ∈ colSpan W (gUp p g), (p : W) • y ∈ A1 := by
      intro y hy
      obtain ⟨w, rfl⟩ := (mem_colSpan (W := W) (gUp p g) y).1 hy
      rw [← psi_apply, smul_psi_gUp h g w]
      exact hle ((mem_colSpan (W := W) g _).2 ⟨w, psi_apply g w⟩)
    obtain ⟨U, rfl⟩ := LatOf_surj h (gUp p g) hgu A1 h1 h2
    exact ⟨⟨U, (hP U).1 hPd, (edge_up_iff p n' k h hq hq1 g hg U).1 hE⟩, rfl⟩

private theorem isEdge_src_le_tgt {k p n' r : ℕ} {e : Edge W Qq k} (h : IsEdge p n' r e) : e.src ≤ e.tgt := by
  unfold IsEdge at h
  exact h.2.2.1

theorem core (p n' : ℕ) (h : Res (p : W) F) (hq : Nat.card F = p ^ n') (N g i : ℕ)
    (gA : Matrix (Fin N) (Fin N) Qq) (hgA : IsUnit gA.det) (gB : Matrix (Fin (N + g)) (Fin (N + g)) Qq)
    (hgB : IsUnit gB.det) (x : Matrix (Fin (N + g)) (Fin N) Qq) :
    Nat.card {B1 : Submodule W (Fin (N + g) → Qq) // IsEdge p n' i ⟨B1, colSpan W gB⟩ ∧
        ∀ y ∈ colSpan W gA, x.mulVec y ∈ B1} =
      ∑ l ∈ Finset.range (i + 1), (p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l *
        Nat.card {A1 : Submodule W (Fin N → Qq) // IsEdge p n' (i - l) ⟨colSpan W gA, A1⟩ ∧
          ∀ y ∈ A1, x.mulVec y ∈ colSpan W gB} := by
  classical
  have hp0 : (p : Qq) ≠ 0 := pQ_ne h
  haveI hFfin : Finite F := by
    apply Nat.finite_of_card_ne_zero
    rw [hq]
    refine pow_ne_zero _ ?_
    rintro rfl
    exact h.ne Nat.cast_zero
  have hq1 : 2 ≤ p ^ n' := by
    rw [← hq]
    exact Finite.one_lt_card
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ n' := by rw [← Nat.card_eq_fintype_card, hq]
  by_cases hx : ∀ y ∈ colSpan W gA, x.mulVec y ∈ colSpan W gB
  swap
  · push_neg at hx
    obtain ⟨y0, hy0, hxy0⟩ := hx
    have hL : Nat.card {B1 : Submodule W (Fin (N + g) → Qq) // IsEdge p n' i ⟨B1, colSpan W gB⟩ ∧
        ∀ y ∈ colSpan W gA, x.mulVec y ∈ B1} = 0 :=
      Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨B1, hE, hB1⟩ => hxy0 (isEdge_src_le_tgt hE (hB1 y0 hy0))⟩)
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨A1, hE, hA1⟩ => hxy0 (hA1 _ (isEdge_src_le_tgt hE hy0))⟩), mul_zero]
  have injB := psi_injective_of_isUnit_det (W := W) gB hgB
  have memA : ∀ w, psi gA w ∈ colSpan W gA := fun w => (mem_colSpan (W := W) gA _).2 ⟨w, psi_apply gA w⟩
  have hex : ∀ w : Fin N → W, ∃ v : Fin (N + g) → W, psi gB v = x.mulVec (psi gA w) := by
    intro w
    obtain ⟨v, hv⟩ := (mem_colSpan (W := W) gB _).1 (hx _ (memA w))
    exact ⟨v, by rw [hv, psi_apply]⟩
  choose T hT using hex
  let Tl : (Fin N → W) →ₗ[W] (Fin (N + g) → W) :=
    { toFun := T
      map_add' := fun a b => injB (by rw [map_add, hT, hT, hT, map_add, Matrix.mulVec_add])
      map_smul' := fun c a => injB (by
        rw [RingHom.id_apply, map_smul, hT, hT, map_smul, Matrix.mulVec_smul]) }
  let Mf : Matrix (Fin (N + g)) (Fin N) F :=
    Matrix.of fun r c => algebraMap W F (T (fun j => if c = j then 1 else 0) r)
  let f : (Fin N → F) →ₗ[F] (Fin (N + g) → F) := Matrix.mulVecLin Mf
  have key : ∀ w, red F (N + g) (Tl w) = f (red F N w) := by
    intro w
    funext r
    rw [LinearMap.pi_apply_eq_sum_univ Tl w]
    simp only [red_apply, f, Mf, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have redSurj : ∀ (m : ℕ) (u : Fin m → F), ∃ w : Fin m → W, red F m w = u := by
    intro m u
    choose w hw using fun c => h.surj (u c)
    exact ⟨w, funext fun c => by rw [red_apply, hw]⟩
  have hL : ∀ w : Fin N → W, x.mulVec (psi (gUp p gA) w) ∈ colSpan W gB ↔ f (red F N w) = 0 := by
    intro w
    have e1 : (p : W) • x.mulVec (psi (gUp p gA) w) = psi gB (T w) := by
      rw [hT, ← smul_psi_gUp h gA w, Matrix.mulVec_smul]
    rw [← key]
    show _ ↔ red F (N + g) (T w) = 0
    rw [red_eq_zero h]
    constructor
    · intro hm
      obtain ⟨v, hv⟩ := (mem_colSpan (W := W) gB _).1 hm
      refine ⟨v, injB ?_⟩
      rw [map_smul, ← e1, hv, psi_apply]
    · rintro ⟨v, hv⟩
      refine (mem_colSpan (W := W) gB _).2 ⟨v, ?_⟩
      rw [← psi_apply]
      rw [hv, map_smul, ← algebraMap_smul Qq (p : W) (x.mulVec _), ← algebraMap_smul Qq (p : W),
        map_natCast] at e1
      exact smul_right_injective (Fin (N + g) → Qq) hp0 e1
  have hPd : ∀ U : Submodule F (Fin (N + g) → F),
      (∀ y ∈ colSpan W gA, x.mulVec y ∈ LatOf (W := W) gB U) ↔ LinearMap.range f ≤ U := by
    intro U
    constructor
    · intro H v hv
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
      obtain ⟨w, rfl⟩ := redSurj N u
      have hm := H _ (memA w)
      rw [← hT, psi_mem_LatOf gB hgB U] at hm
      change red F (N + g) (Tl w) ∈ U at hm
      rwa [key] at hm
    · intro H y hy
      obtain ⟨w, rfl⟩ := (mem_colSpan (W := W) gA y).1 hy
      rw [← psi_apply, ← hT, psi_mem_LatOf gB hgB U]
      change red F (N + g) (Tl w) ∈ U
      rw [key]
      exact H (LinearMap.mem_range_self f _)
  have hPu : ∀ U : Submodule F (Fin N → F),
      (∀ y ∈ LatOf (W := W) (gUp p gA) U, x.mulVec y ∈ colSpan W gB) ↔ U ≤ LinearMap.ker f := by
    intro U
    constructor
    · intro H u hu
      obtain ⟨w, rfl⟩ := redSurj N u
      exact LinearMap.mem_ker.2 ((hL w).1 (H _ ((psi_mem_LatOf (gUp p gA) (gUp_det h gA hgA) U w).2 hu)))
    · intro H y hy
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
      exact (hL w).2 (LinearMap.mem_ker.1 (H hw))
  have hdown : Nat.card {B1 : Submodule W (Fin (N + g) → Qq) // IsEdge p n' i ⟨B1, colSpan W gB⟩ ∧
        ∀ y ∈ colSpan W gA, x.mulVec y ∈ B1} =
      Nat.card {U : Submodule F (Fin (N + g) → F) // LinearMap.range f ≤ U ∧ Module.finrank F U + i = N + g} :=
    down_card p n' i h hq hq1 gB hgB (fun B1 => ∀ y ∈ colSpan W gA, x.mulVec y ∈ B1)
      (fun U => LinearMap.range f ≤ U) hPd
  have hup : ∀ l, Nat.card {A1 : Submodule W (Fin N → Qq) // IsEdge p n' (i - l) ⟨colSpan W gA, A1⟩ ∧
      ∀ y ∈ A1, x.mulVec y ∈ colSpan W gB} = Formalism.G0.countBelow (LinearMap.ker f) (i - l) :=
    fun l => up_card p n' (i - l) h hq hq1 gA hgA (fun A1 => ∀ y ∈ A1, x.mulVec y ∈ colSpan W gB)
      (fun U => U ≤ LinearMap.ker f) hPu
  rw [hdown]
  simp only [hup]
  have hT2 := Formalism.G0.countAboveRangeCodimFormula f N g i (Module.finrank_fin_fun F) (Module.finrank_fin_fun F)
  rw [hcardF] at hT2
  exact_mod_cast hT2

end Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G

theorem countLoc : CountLoc := by
  intro p n' W Qq _ _ _ _ _ hfr hirr hcard N N' g i hN A B hA hB x
  subst hN
  obtain ⟨gA, hgA, rfl⟩ := hA
  obtain ⟨gB, hgB, rfl⟩ := hB
  haveI := hfr
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  have hres : Cnt.Res (p : W) (W ⧸ Ideal.span {(p : W)}) :=
    { surj := by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
      ker := fun w => by
        rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      ne := hirr.ne_zero }
  exact Cnt.core p n' hres hcard N g i gA hgA gB hgB x

end Formalism.MainNotions.FormalGroupSystem.Pf
