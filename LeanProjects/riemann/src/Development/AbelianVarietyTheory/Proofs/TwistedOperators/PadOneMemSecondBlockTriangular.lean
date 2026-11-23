import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DiagonalPaddingLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiagLiftFix

theorem exists_char_sep {G : Type} [AddCommGroup G] (L : AddSubgroup G) [Finite (G ⧸ L)] {y : G} (hy : y ∉ L) :
    ∃ χ : AddChar G ℂ, (∀ l ∈ L, χ l = 1) ∧ χ y ≠ 1 := by
  have hq : (QuotientAddGroup.mk y : G ⧸ L) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.2 hq
  refine ⟨ψ.compAddMonoidHom (QuotientAddGroup.mk' L), fun l hl => ?_, hψ⟩
  show ψ (QuotientAddGroup.mk' L l) = 1
  rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff l).2 hl, AddChar.map_zero_eq_one]

theorem eq_top_of_sep {G : Type} [AddCommGroup G] [Finite G] (K : AddSubgroup (AddChar G ℂ))
    (h : ∀ g, (∀ χ ∈ K, χ g = 1) → g = 0) : K = ⊤ := by
  by_contra hK
  obtain ⟨φ, -, hφ⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hK)
  obtain ⟨Φ, hΦK, hΦ⟩ := exists_char_sep K hφ
  obtain ⟨g, rfl⟩ := (AddChar.doubleDualEmb_bijective (α := G)).2 Φ
  have hg : g = 0 := h g (fun χ hχ => by simpa using hΦK χ hχ)
  subst hg
  exact hΦ (by simp)

theorem exists_dual_sep {G : Type} [AddCommGroup G] {χ : G → G → ℂ} (h : GlobalTheory.PlaceModel.IsBichar χ)
    {X Y L₀ L₀' L : AddSubgroup G} (hL₀' : L₀' ≤ Y) (hLL' : ∀ u ∈ L₀, ∀ y ∈ L₀', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L₀', χ x y = 1) → x ∈ L₀)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u)
    (hL : L ≤ X) {M : ℕ} (hM : 0 < M) (h1 : ∀ u ∈ L, M • u ∈ L₀) (h2 : ∀ u ∈ L₀, M • u ∈ L)
    {x : G} (hx : x ∈ X) (hxM : M • x ∈ L₀) (hxL : x ∉ L) :
    ∃ y ∈ Y, (∀ u ∈ L, χ u y = 1) ∧ χ x y ≠ 1 := by
  classical

  obtain ⟨W, memW⟩ : ∃ W : AddSubgroup G, ∀ u, u ∈ W ↔ u ∈ X ∧ M • u ∈ L₀ :=
    ⟨X ⊓ L₀.comap (nsmulAddMonoidHom M), fun u => by simp⟩
  obtain ⟨N, memN⟩ : ∃ N : AddSubgroup W, ∀ u : W, u ∈ N ↔ ∃ v ∈ L₀, M • v = (u : G) :=
    ⟨(L₀.map (nsmulAddMonoidHom M)).addSubgroupOf W, fun u => by simp [AddSubgroup.mem_addSubgroupOf]⟩
  obtain ⟨R, hRf, hR⟩ := hfin (M * M) (Nat.mul_pos hM hM)
  have key : ∀ u : W, ∃ r ∈ R, ∃ v ∈ L₀, M • (u : G) = r + (M * M) • v := fun u =>
    hR _ ((memW u).1 u.2).2
  have sameR : ∀ (u u' : W) (r v v' : G), v ∈ L₀ → v' ∈ L₀ → M • (u : G) = r + (M * M) • v →
      M • (u' : G) = r + (M * M) • v' → (QuotientAddGroup.mk u : W ⧸ N) = QuotientAddGroup.mk u' := by
    intro u u' r v v' hv hv' e e'
    rw [QuotientAddGroup.eq, memN]
    refine ⟨v' - v, L₀.sub_mem hv' hv, tf M hM ?_⟩
    show M • M • (v' - v) = M • (-(u : G) + (u' : G))
    rw [smul_add, smul_neg, e, e', ← mul_smul, smul_sub]
    abel
  haveI : Finite (W ⧸ N) := by
    haveI : Finite R := hRf.to_subtype
    let g : R → W ⧸ N := fun r =>
      if h : ∃ u : W, ∃ v ∈ L₀, M • (u : G) = (r : G) + (M * M) • v then QuotientAddGroup.mk h.choose else 0
    refine Finite.of_surjective g fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, v, hv, e⟩ := key u
    have hex : ∃ u : W, ∃ v ∈ L₀, M • (u : G) = ((⟨r, hr⟩ : R) : G) + (M * M) • v := ⟨u, v, hv, e⟩
    refine ⟨⟨r, hr⟩, ?_⟩
    dsimp only [g]
    rw [dif_pos hex]
    obtain ⟨v', hv', e'⟩ := hex.choose_spec
    exact sameR _ _ r v' v hv' hv e' e

  have hφ : ∀ y : G, M • y ∈ L₀' → ∃ φ : AddChar (W ⧸ N) ℂ, ∀ u : W, φ (QuotientAddGroup.mk u) = χ u y := by
    intro y hy
    let f : W →+ Additive ℂ :=
      { toFun := fun u => Additive.ofMul (χ u y)
        map_zero' := congrArg Additive.ofMul (h.zero_left y)
        map_add' := fun a b => congrArg Additive.ofMul (h.left a b y) }
    have hNk : N ≤ f.ker := by
      intro u hu
      obtain ⟨v, hv, e⟩ := (memN u).1 hu
      rw [AddMonoidHom.mem_ker]
      show Additive.ofMul (χ (u : G) y) = 0
      rw [← e, h.nsmul]
      exact congrArg Additive.ofMul (hLL' v hv _ hy)
    exact ⟨AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N f hNk), fun u => rfl⟩

  have inv_eq : ∀ (u y : G), χ (-u) y = χ u (-y) := by
    intro u y
    have h1 := h.neg_mul u y
    have h2 : χ u (-y) * χ u y = 1 := by rw [← h.right, neg_add_cancel, h.zero_right]
    have hc : χ u y ≠ 0 := right_ne_zero_of_mul_eq_one h1
    exact mul_right_cancel₀ hc (h1.trans h2.symm)
  let K : AddSubgroup (AddChar (W ⧸ N) ℂ) :=
    { carrier := {φ | ∃ y ∈ Y, M • y ∈ L₀' ∧ ∀ u : W, φ (QuotientAddGroup.mk u) = χ u y}
      zero_mem' := ⟨0, Y.zero_mem, by rw [smul_zero]; exact L₀'.zero_mem, fun u => by
        rw [AddChar.zero_apply, h.zero_right]⟩
      add_mem' := by
        rintro φ₁ φ₂ ⟨y₁, hy₁, hm₁, e₁⟩ ⟨y₂, hy₂, hm₂, e₂⟩
        refine ⟨y₁ + y₂, Y.add_mem hy₁ hy₂, by rw [smul_add]; exact L₀'.add_mem hm₁ hm₂, fun u => ?_⟩
        rw [AddChar.add_apply, e₁, e₂, h.right]
      neg_mem' := by
        rintro φ ⟨y, hy, hm, e⟩
        refine ⟨-y, Y.neg_mem hy, by rw [smul_neg]; exact L₀'.neg_mem hm, fun u => ?_⟩
        rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, e]
        exact inv_eq u y }
  have hK : K = ⊤ := by
    refine eq_top_of_sep K fun q hq => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨v, hvX, hv⟩ := dX M hM u ((memW u).1 u.2).1
    have hvL : v ∈ L₀ := by
      refine hX v hvX fun y'' hy'' => ?_
      obtain ⟨y, hyY, hy⟩ := dY M hM y'' (hL₀' hy'')
      obtain ⟨φ, hφu⟩ := hφ y (hy ▸ hy'')
      have hφK : φ ∈ K := ⟨y, hyY, hy ▸ hy'', hφu⟩
      rw [← hy, ← h.nsmul, hv, ← hφu]
      exact hq φ hφK
    exact (QuotientAddGroup.eq_zero_iff u).2 ((memN u).2 ⟨v, hvL, hv⟩)

  have hxW : x ∈ W := (memW x).2 ⟨hx, hxM⟩
  let Lb : AddSubgroup (W ⧸ N) := (L.addSubgroupOf W).map (QuotientAddGroup.mk' N)
  have hxb : (QuotientAddGroup.mk (⟨x, hxW⟩ : W) : W ⧸ N) ∉ Lb := by
    rintro ⟨l, hl, hlx⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq, memN] at hlx
    obtain ⟨v, hv, e⟩ := hlx
    apply hxL
    have hx' : x = (l : G) + M • v := by
      rw [e]
      show x = (l : G) + (-(l : G) + x)
      abel
    rw [hx']
    exact L.add_mem (AddSubgroup.mem_addSubgroupOf.1 hl) (h2 v hv)
  obtain ⟨ψ, hψL, hψx⟩ := exists_char_sep Lb hxb
  have hψK : ψ ∈ K := hK ▸ AddSubgroup.mem_top ψ
  obtain ⟨y, hyY, -, hψ⟩ := hψK
  refine ⟨y, hyY, fun u hu => ?_, ?_⟩
  · have huW : u ∈ W := (memW u).2 ⟨hL hu, h1 u hu⟩
    rw [← hψ ⟨u, huW⟩]
    exact hψL _ ⟨⟨u, huW⟩, AddSubgroup.mem_addSubgroupOf.2 hu, rfl⟩
  · rw [← hψ ⟨x, hxW⟩]
    exact hψx

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem isLattice_of_isFrame {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) : Submodule.IsLattice E Λ := by
  classical
  letI : StarRing E := starRingOfComm
  set ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) with hι

  have hspan : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.L2.Herm.hatL (F := F) M =
      Submodule.span (Formalism.L2.Herm.intAf F E) ((fun x : Fin n → E => fun i => ι (x i)) '' (M : Set (Fin n → E))) :=
    fun M => rfl

  have hstd : ∀ y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, (∀ i, y i ∈ Formalism.L2.Herm.intAf F E) →
      y ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.BasicNotions.Examples₂.stdLat (E := E) n) := by
    intro y hy
    have hy' : y = ∑ i, (⟨y i, hy i⟩ : Formalism.L2.Herm.intAf F E) • (fun j => ι (Pi.basisFun E (Fin n) i j)) := by
      ext j
      simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, apply_ite, Subring.smul_def]
    rw [hy', hspan]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    exact Submodule.subset_span ⟨i, rfl⟩
  have hL0 := Formalism.BasicNotions.Examples₂.stdLat_isLattice (E := E) n
  have hL' : Submodule.IsLattice E (Formalism.UG.CS.globLat (F := F) β (Formalism.BasicNotions.Examples₂.stdLat (E := E) n)) :=
    Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.mpr hL0.fg) hL0.span_eq_top β
  have hgen : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    intro x hx
    rw [hspan]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

  have hle : Λ ≤ Formalism.UG.CS.globLat (F := F) β (Formalism.BasicNotions.Examples₂.stdLat (E := E) n) := by
    intro x hx
    exact hstd _ ((hβ _).1 (hgen x hx))
  refine ⟨Submodule.FG.of_le hL'.fg hle, ?_⟩

  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have hall : ∀ e : E, IsIntegral ℤ e := by
      intro e
      apply Formalism.UG.P.csGlob_int (F := F)
      have he : ι e = 0 := by
        have : e = a * (a⁻¹ * e) := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        rw [this, map_mul, ha, zero_mul]
      show ι e ∈ Formalism.L2.Herm.intAf F E
      rw [he]
      exact Subring.zero_mem _
    have h2 := hall (algebraMap ℚ E (1 / 2))
    rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at h2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    have hy' : (y : ℚ) = 1 / 2 := by simpa using hy
    have h3 : ((2 * y : ℤ) : ℚ) = 1 := by push_cast; rw [hy']; norm_num
    have h4 : (2 * y : ℤ) = 1 := by exact_mod_cast h3
    omega

  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hfΛ : ∀ x ∈ Λ, f x = 0 := by
    intro x hx
    have : f x ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f := ⟨x, Submodule.subset_span hx, rfl⟩
    rw [hf] at this
    exact this
  set c : Fin n → E := fun i => f (fun j => if i = j then 1 else 0) with hc
  have hfx : ∀ x : Fin n → E, f x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    rfl
  have hφ : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∑ i, y i * ι (c i) = 0 := by
    intro y hy
    rw [hspan] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      calc ∑ i, ι (x i) * ι (c i) = ι (∑ i, x i * c i) := by simp [map_sum, map_mul]
        _ = 0 := by rw [← hfx, hfΛ x hx, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp [add_mul, Finset.sum_add_distrib, hy, hz]
    | smul s y _ hy =>
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hy, mul_zero]
  have hcol : ∀ j, (fun i => (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := by
    intro j
    refine (hβ _).2 (fun i => ?_)
    have h1 : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (fun i => (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) i =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j := by
      rw [← h1]
      rfl
    rw [h2, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hv : Matrix.vecMul (fun i => ι (c i)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 0 := by
    ext j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← hφ _ (hcol j)]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hv0 : (fun i => ι (c i)) = 0 := by
    have h1 : (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (fun i => ι (c i)) = Matrix.vecMul (fun i => ι (c i))
          ((β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
          rw [h1, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  have hc0 : ∀ i, c i = 0 := fun i => hinj (by rw [map_zero]; exact congrFun hv0 i)
  apply hf0
  refine LinearMap.ext (fun x => ?_)
  rw [hfx x, LinearMap.zero_apply]
  simp [hc0]

end Frame

section Mat

open GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPaddingLift GlobalTheory.StepLaw.TypeDatum

variable {κ : Type} [CommRing κ] {r a b : ℕ}

end Mat

section Dat

open GlobalTheory.StepLaw.TypeDatum

variable {D : D7} {a b : ℕ} (L : LevDat D.host.E ℂ a) (hL : L.P = LevelP.triv L.Pg L.r ℂ)
  (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

include hL

end Dat

section Dual

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D}

def dualLat (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | a • w ∈ Λ ∧ (∀ u ∈ Λ, IsHalf a u → ψ (symplO S T u w) = 1) ∧ (a + cA D a) • w = w}
  zero_mem' := ⟨by rw [smul_zero]; exact zero_mem _, fun u _ _ => (isBichar_symplO S T ψ).zero_right u, smul_zero _⟩
  add_mem' := by
    rintro x y ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
    refine ⟨by rw [smul_add]; exact add_mem x1 y1, fun u hu hh => ?_, by rw [smul_add, x3, y3]⟩
    rw [symplO_add_right, AddChar.map_add_eq_mul, x2 u hu hh, y2 u hu hh, mul_one]
  neg_mem' := by
    rintro x ⟨x1, x2, x3⟩
    refine ⟨by rw [smul_neg]; exact neg_mem x1, fun u hu hh => ?_, by rw [smul_neg, x3]⟩
    have h := ψ.map_add_eq_mul (symplO S T u x) (symplO S T u (-x))
    rw [← symplO_add_right, add_neg_cancel x, symplO_zero_right, AddChar.map_zero_eq_one, x2 u hu hh, one_mul] at h
    exact h.symm

variable {ψ : AddChar (AF D.host.F) ℂ} {a : AE D} {Λ : AddSubgroup (WO S T)}

theorem smul_eq_of_half {u : WO S T} (h : IsHalf a u) : a • u = u := by
  ext i j
  exact h i j

theorem half_of_smul_eq {u : WO S T} (h : a • u = u) : IsHalf a u := by
  intro i j
  exact congrArg (fun M : WO S T => M i j) h

theorem half_smul {e : AE D} (h : a * e = e) (u : WO S T) : IsHalf a (e • u) := by
  intro i j
  show a * (e * u i j) = e * u i j
  rw [← mul_assoc, h]

theorem mem_dualLat_half (hc : a * cA D a = 0) {w : WO S T} (hw : IsHalf a w) : w ∈ dualLat ψ a Λ ↔ w ∈ Λ := by
  have hw' : a • w = w := smul_eq_of_half hw
  have hz : cA D a • w = 0 := by
    rw [← hw', smul_smul, mul_comm, hc, zero_smul]
  change a • w ∈ Λ ∧ (∀ u ∈ Λ, IsHalf a u → ψ (symplO S T u w) = 1) ∧ (a + cA D a) • w = w ↔ w ∈ Λ
  rw [add_smul, hz, add_zero, hw']
  refine ⟨fun h => h.1, fun h => ⟨h, fun u _ hu => ?_, rfl⟩⟩
  rw [← smul_eq_of_half hu, symplO_smul, hz, symplO_zero_right, AddChar.map_zero_eq_one]

theorem mem_dualLat_conj (hc : a * cA D a = 0) {w : WO S T} (hw : IsHalf (cA D a) w) :
    w ∈ dualLat ψ a Λ ↔ ∀ u ∈ Λ, IsHalf a u → ψ (symplO S T u w) = 1 := by
  have hw' : cA D a • w = w := smul_eq_of_half hw
  have hz : a • w = 0 := by
    rw [← hw', smul_smul, hc, zero_smul]
  change a • w ∈ Λ ∧ (∀ u ∈ Λ, IsHalf a u → ψ (symplO S T u w) = 1) ∧ (a + cA D a) • w = w ↔
    ∀ u ∈ Λ, IsHalf a u → ψ (symplO S T u w) = 1
  rw [add_smul, hz, hw', zero_add]
  exact ⟨fun h => h.2.1, fun h => ⟨Λ.zero_mem, h, rfl⟩⟩

theorem dualLat_isotropic (ha : a * a = a) {u w : WO S T} (hu : u ∈ dualLat ψ a Λ) (hw : w ∈ dualLat ψ a Λ) :
    ψ (symplO S T u w) = 1 := by
  have hu' : a • u ∈ Λ ∧ (∀ v ∈ Λ, IsHalf a v → ψ (symplO S T v u) = 1) ∧ (a + cA D a) • u = u := hu
  have hw' : a • w ∈ Λ ∧ (∀ v ∈ Λ, IsHalf a v → ψ (symplO S T v w) = 1) ∧ (a + cA D a) • w = w := hw
  have h1 : ψ (symplO S T (a • u) w) = 1 := hw'.2.1 _ hu'.1 (half_smul ha u)
  have h2 : ψ (symplO S T (a • w) u) = 1 := hu'.2.1 _ hw'.1 (half_smul ha w)
  have key : symplO S T u w = symplO S T (a • u) w + -symplO S T (a • w) u := by
    conv_lhs => rw [← hu'.2.2]
    rw [add_smul, symplO_add_left, symplO_skew S T w (cA D a • u), ← symplO_smul S T a w u]
  rw [key, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, h2, inv_one, mul_one]

theorem isSBHalf_dualLat (hc : a * cA D a = 0) (Φ : WO S T → ℂ) :
    IsSBHalf a (dualLat ψ a Λ) Φ ↔ IsSBHalf a Λ Φ := by
  have hk : ∀ (k : ℕ) (t : WO S T), IsHalf a t → IsHalf a (k • t) := fun k t ht =>
    half_of_smul_eq (by rw [smul_comm, smul_eq_of_half ht])
  unfold IsSBHalf
  constructor
  · rintro ⟨h1, k, hk0, h2, h3⟩
    exact ⟨h1, k, hk0, fun u hu hh t => h2 u ((mem_dualLat_half hc hh).2 hu) hh t,
      fun t ht => (mem_dualLat_half hc (hk k t (h1 t ht))).1 (h3 t ht)⟩
  · rintro ⟨h1, k, hk0, h2, h3⟩
    exact ⟨h1, k, hk0, fun u hu hh t => h2 u ((mem_dualLat_half hc hh).1 hu) hh t,
      fun t ht => (mem_dualLat_half hc (hk k t (h1 t ht))).2 (h3 t ht)⟩

theorem halfInd_dualLat (hc : a * cA D a = 0) : halfInd a (dualLat ψ a Λ) = halfInd a Λ := by
  unfold halfInd
  funext t
  by_cases ht : IsHalf a t
  · have e := mem_dualLat_half (ψ := ψ) (Λ := Λ) hc ht
    by_cases h : t ∈ Λ
    · rw [if_pos ⟨e.2 h, ht⟩, if_pos ⟨h, ht⟩]
    · rw [if_neg (fun h' => h (e.1 h'.1)), if_neg (fun h' => h h'.1)]
  · rw [if_neg (fun h' => ht h'.2), if_neg (fun h' => ht h'.2)]

theorem isPlaceModel_dualLat (hc : a * cA D a = 0) {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (dualLat ψ a Λ) 1 f₀ Tm := by
  refine { trans := fun Φ hΦ x hx => h.trans Φ ((isSBHalf_dualLat hc Φ).1 hΦ) x hx,
           modul := fun Φ hΦ y hy => h.modul Φ ((isSBHalf_dualLat hc Φ).1 hΦ) y hy,
           vac := ?_ }
  rw [halfInd_dualLat hc]
  exact h.vac

end Dual

section Lat

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem idem_smul_mem {a : AE D} (ha : a * a = a) {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    a • u ∈ latO S T ΛS ΛT fun _ => True := by
  exact (AddSubgroup.mem_inf.1 (GlobalTheory.PlaceModelSum.idem_smul_half ha hu)).1

theorem exists_nsmul_latO (hS : ΛS.FG) (hT : ΛT.FG) (hS' : Submodule.IsLattice D.host.E ΛS')
    (hT' : Submodule.IsLattice D.host.E ΛT') :
    ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True, M • u ∈ latO S T ΛS' ΛT' fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS hT
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS' hT'
  refine ⟨K * M, Nat.mul_pos hK hM, fun u hu => ?_⟩
  rw [mul_smul]
  have h0 := GlobalTheory.SplitScalar.latO_fin hu
  refine hKt (M • u) ?_ ?_
  · ext i j
    have h1 := congrFun (congrFun h0 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1 ⊢
    rw [Matrix.smul_apply, map_nsmul, h1, smul_zero]
  · intro i j
    rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
    exact hMu u hu i j

theorem half_finite_mod (hS : ΛS.FG) (hT : ΛT.FG) {a : AE D} (ha : a * a = a) (k : ℕ) (hk : 0 < k) :
    ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a,
      ∃ r ∈ R, ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a, t = r + k • u := by
  obtain ⟨R, hR, hRt⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS hT (fun _ => True) k hk
  refine ⟨(fun r => a • r) '' R, hR.image _, fun t ht => ?_⟩
  have ht1 := (AddSubgroup.mem_inf.1 ht).1
  have ht2 : a • t = t := (AddSubgroup.mem_inf.1 ht).2
  obtain ⟨r, hr, u, hu, rfl⟩ := hRt t ht1
  refine ⟨a • r, Set.mem_image_of_mem _ hr, a • u, GlobalTheory.PlaceModelSum.idem_smul_half ha hu, ?_⟩
  rw [← ht2, smul_add, smul_comm a k u]

private theorem symplO_nsmul_left_eq_nsmul_right (n : ℕ) (x y : WO S T) :
    symplO S T (n • x) y = symplO S T x (n • y) := by
  induction n with
  | zero => simp only [zero_smul, GlobalTheory.PlaceModel.symplO_zero_left, GlobalTheory.PlaceModel.symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, ih]

theorem latO_bidual (hψ : IsStdChar D ψ (-1)) (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0) (x : WO S T)
    (hx : IsHalf a x) (hn : x ∉ latO S T ΛS ΛT fun _ => True) :
    ∃ y, IsHalf (cA D a) y ∧ (∀ u ∈ latO S T ΛS ΛT fun _ => True, IsHalf a u → ψ (symplO S T u y) = 1) ∧
      ψ (symplO S T x y) ≠ 1 := by
  classical
  have hSf := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hTf := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have hSl : Submodule.IsLattice D.host.E (GlobalTheory.PlaceModel.latFrame S) := hSf.1
  have hTl : Submodule.IsLattice D.host.E (GlobalTheory.PlaceModel.latFrame T) := hTf.1
  have hI := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) hψ hSf hTf).1
  have hmap : ∀ u : WO S T, IsHalf a u → u.map (infPart D) = 0 := by
    intro u hu
    rw [← smul_eq_of_half hu]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hinf]
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, ha]
  have hpair : ∀ u ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf a u →
      ∀ y ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u y) = 1 :=
    fun u hu hua y hy => (hI u (hmap u hua)).1 hu y hy
  have hbid : ∀ z : WO S T, IsHalf a z →
      (∀ y ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D a) y →
        ψ (symplO S T z y) = 1) →
      z ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro z hz h
    apply (hI z (hmap z hz)).2
    intro u' hu'
    rw [← smul_eq_of_half hz, GlobalTheory.PlaceModel.symplO_smul]
    exact h _ (idem_smul_mem (ΛS := GlobalTheory.PlaceModel.latFrame S) (ΛT := GlobalTheory.PlaceModel.latFrame T) hcc hu')
      (half_smul hcc u')
  obtain ⟨M1, hM1, h1⟩ := exists_nsmul_latO (ΛS := ΛS) (ΛT := ΛT) (ΛS' := GlobalTheory.PlaceModel.latFrame S)
    (ΛT' := GlobalTheory.PlaceModel.latFrame T) hS.fg hT.fg hSl hTl
  obtain ⟨M2, hM2, h2⟩ := exists_nsmul_latO (ΛS := GlobalTheory.PlaceModel.latFrame S) (ΛT := GlobalTheory.PlaceModel.latFrame T)
    (ΛS' := ΛS) (ΛT' := ΛT) hSl.fg hTl.fg hS hT
  have hmul : ∀ u : WO S T, (M1 * M2) • u = M2 • (M1 • u) := fun u => by
    rw [mul_comm, mul_smul]
  have hmul' : ∀ u : WO S T, (M1 * M2) • u = M1 • (M2 • u) := fun u => mul_smul M1 M2 u
  have hXi : ∀ u : WO S T, IsHalf a u → u ∈ GlobalTheory.PlaceModel.half S T a := fun u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).1 hu
  have hXo : ∀ u : WO S T, u ∈ GlobalTheory.PlaceModel.half S T a → IsHalf a u := fun u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
  have hMpos : 0 < M1 * M2 := Nat.mul_pos hM1 hM2
  have hx' : x ∈ GlobalTheory.PlaceModel.half S T a := hXi x hx
  by_cases hxM : (M1 * M2) • x ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a
  · obtain ⟨y, hyY, hyL, hxy⟩ := exists_dual_sep (χ := fun u v : WO S T => ψ (symplO S T u v))
      (GlobalTheory.PlaceModel.isBichar_symplO S T ψ)
      (X := GlobalTheory.PlaceModel.half S T a) (Y := GlobalTheory.PlaceModel.half S T (cA D a))
      (L₀ := (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
        (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a)
      (L₀' := (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
        (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T (cA D a))
      (L := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓
        GlobalTheory.PlaceModel.half S T a)
      inf_le_right
      (fun u hu y hy => hpair u hu.1 (hXo u hu.2) y hy.1)
      (fun z hz h => ⟨hbid z (hXo z hz) (fun y hy hyh =>
        h y ⟨hy, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hyh⟩), hz⟩)
      (fun k hk z hz => GlobalTheory.PlaceModel.half_div S T a k hk z hz)
      (fun k hk z hz => GlobalTheory.PlaceModel.half_div S T (cA D a) k hk z hz)
      (fun k hk t t' h => by
        have e := congrArg (fun z : WO S T => incA D ((k : D.host.E))⁻¹ • z) h
        simpa only [GlobalTheory.PlaceModel.inv_smul_nsmul S T hk] using e)
      (fun k hk => half_finite_mod (ΛS := GlobalTheory.PlaceModel.latFrame S) (ΛT := GlobalTheory.PlaceModel.latFrame T)
        hSl.fg hTl.fg ha k hk)
      inf_le_right hMpos
      (fun u hu => ⟨by rw [hmul]; exact AddSubgroup.nsmul_mem _ (h1 u hu.1) _,
        AddSubgroup.nsmul_mem _ hu.2 _⟩)
      (fun u hu => ⟨by rw [hmul']; exact AddSubgroup.nsmul_mem _ (h2 u hu.1) _,
        AddSubgroup.nsmul_mem _ hu.2 _⟩)
      hx' hxM (fun h => hn h.1)
    exact ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).2 hyY, fun u hu hua => hyL u ⟨hu, hXi u hua⟩, hxy⟩
  · have hMx : (M1 * M2) • x ∈ GlobalTheory.PlaceModel.half S T a := AddSubgroup.nsmul_mem _ hx' _
    have hnot : ¬ ∀ y ∈ (latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
        (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D a) y →
          ψ (symplO S T ((M1 * M2) • x) y) = 1 := fun h => hxM ⟨hbid _ (hXo _ hMx) h, hMx⟩
    push_neg at hnot
    obtain ⟨y, hyL, hyY, hy1⟩ := hnot
    refine ⟨(M1 * M2) • y, ?_, ?_, ?_⟩
    · exact (GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.nsmul_mem _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hyY) _)
    · intro u hu hua
      rw [← symplO_nsmul_left_eq_nsmul_right]
      exact hpair _ (by rw [hmul]; exact AddSubgroup.nsmul_mem _ (h1 u hu) _)
        (hXo _ (AddSubgroup.nsmul_mem _ (hXi u hua) _)) y hyL
    · rw [← symplO_nsmul_left_eq_nsmul_right]
      exact hy1

private theorem isThetaFunO_zero_twisted_operators : IsThetaFunO ψ S T (0 : WO S T → ℂ) := by
  constructor
  case quasi => intro γ w; simp
  case level =>
    refine ⟨⊤, ?_, fun u _ _ => ?_⟩
    · rw [AddSubgroup.coe_top]; exact isOpen_univ
    · rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]
  case cont => exact continuous_const
  case smooth => intro k L _ _ w; exact contDiff_const

private theorem isThetaFunO_add_twisted_operators {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨V, hV, hVg⟩ := hg.level
  constructor
  case quasi => intro γ w; simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
  case level =>
    refine ⟨U ⊓ V, ?_, fun u hu h0 => ?_⟩
    · rw [AddSubgroup.coe_inf]; exact hU.inter hV
    · rw [← GlobalTheory.SplitScalar.heisL_apply, map_add, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply,
        hUf u hu.1 h0, hVg u hu.2 h0]
  case cont => exact hf.cont.add hg.cont
  case smooth => intro k L hL hL0 w; exact (hf.smooth k L hL hL0 w).add (hg.smooth k L hL hL0 w)

private theorem isThetaFunO_smul_twisted_operators (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  constructor
  case quasi => intro γ w; simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]; ring
  case level => exact ⟨U, hU, fun u hu h0 => by rw [GlobalTheory.SplitScalar.heisO_smul, hUf u hu h0]⟩
  case cont => exact hf.cont.const_smul c
  case smooth => intro k L hL hL0 w; exact (hf.smooth k L hL hL0 w).const_smul c

theorem isTheta_placeModel (hψ : IsStdChar D ψ (-1)) (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D} (ha : a * a = a) (hc : a * cA D a = 0) (hinf : infPart D a = 0)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) (Φ : WO S T → ℂ)
    (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : IsThetaFunO ψ S T (Tm Φ) := by
  classical
  have hinf' : infPart D (cA D a) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hmapE : ∀ b : AE D, infPart D b = 0 → ∀ u : WO S T, IsHalf b u → u.map (infPart D) = 0 := by
    intro b hb u hu
    rw [← smul_eq_of_half hu]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hb]
  have hSf := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hTf := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have hSl : Submodule.IsLattice D.host.E (GlobalTheory.PlaceModel.latFrame S) := hSf.1
  have hTl : Submodule.IsLattice D.host.E (GlobalTheory.PlaceModel.latFrame T) := hTf.1
  have hI := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) hψ hSf hTf).1
  obtain ⟨M1, hM1, h1⟩ := exists_nsmul_latO (ΛS := ΛS) (ΛT := ΛT) (ΛS' := GlobalTheory.PlaceModel.latFrame S)
    (ΛT' := GlobalTheory.PlaceModel.latFrame T) hS.fg hT.fg hSl hTl
  have hTd := isPlaceModel_dualLat (ψ := ψ) hc hTm
  have hΦd := (isSBHalf_dualLat (ψ := ψ) (Λ := latO S T ΛS ΛT fun _ => True) hc Φ).2 hΦ
  refine GlobalTheory.SchrTheta.placeModel_induction ψ (e := a) (dualLat ψ a (latO S T ΛS ΛT fun _ => True))
    ?_ ?_ ?_ ?_ hTd (fun f => IsThetaFunO ψ S T f) isThetaFunO_zero_twisted_operators (fun f g hf hg => isThetaFunO_add_twisted_operators hf hg)
    (fun c f hf => isThetaFunO_smul_twisted_operators c hf) ?_ ?_ hf₀ hΦd
  · intro u hu y hy
    exact dualLat_isotropic ha hu.1 hy.1
  · intro x hx h
    have hxh : IsHalf a x := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hx
    refine ⟨(mem_dualLat_half (ψ := ψ) hc hxh).2 ?_, hx⟩
    by_contra hn
    obtain ⟨y, hy, hyL, hxy⟩ := latO_bidual hψ hS hT ha hinf x hxh hn
    exact hxy (h y ⟨(mem_dualLat_conj (ψ := ψ) hc hy).2 hyL, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩)
  · intro k hk
    obtain ⟨R, hR, hRt⟩ := half_finite_mod hS.fg hT.fg ha k hk
    refine ⟨R, hR, fun t ht => ?_⟩
    have ht' : t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a :=
      ⟨(mem_dualLat_half (ψ := ψ) hc ((GlobalTheory.PlaceModel.isHalf_iff S T).2 ht.2)).1 ht.1, ht.2⟩
    obtain ⟨r, hr, u, hu, htu⟩ := hRt t ht'
    exact ⟨r, hr, u, ⟨(mem_dualLat_half (ψ := ψ) hc ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2)).2 hu.1, hu.2⟩, htu⟩
  · intro y hy
    have hyh : IsHalf (cA D a) y := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hy
    obtain ⟨k0, hk0, hky⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hSl hTl y (hmapE _ hinf' y hyh)
    refine ⟨M1 * k0, Nat.mul_pos hM1 hk0, ?_⟩
    have hyk : IsHalf (cA D a) ((M1 * k0) • y) :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.nsmul_mem _ hy _)
    refine (mem_dualLat_conj (ψ := ψ) hc hyk).2 (fun u hu hua => ?_)
    rw [mul_smul, ← symplO_nsmul_left_eq_nsmul_right]
    have hMuh : IsHalf a (M1 • u) :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.nsmul_mem _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hua) _)
    exact (hI (M1 • u) (hmapE a hinf _ hMuh)).1 (h1 u hu) (k0 • y) hky
  · intro x hx f hf
    exact GlobalTheory.SchrTheta.isTheta_heis_fin hψ hf (hmapE a hinf x ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hx))
  · intro y hy f hf
    exact GlobalTheory.SchrTheta.isTheta_heis_fin hψ hf (hmapE _ hinf' y ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hy))

end Lat

section Idem

variable {D : D7} {a e : AE D} {P : Finset (Pl D.host.E)} {PP : Pl D.host.E}

theorem resS_mul_eq_zero {x y : AE D} (hx : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : toEAf D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h : x * y = 0) (Q : Pl D.host.E)
    (h1 : resS D.host.F Q ⟨_, hx⟩ = 1) : resS D.host.F Q ⟨_, hy⟩ = 0 := by
  have hxy : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨_, hy⟩ = 0 := by
    apply Subtype.ext
    show toEAf D x * toEAf D y = 0
    rw [← map_mul, h, map_zero]
  have h2 := congrArg (resS D.host.F Q) hxy
  rw [map_mul, map_zero, h1, one_mul] at h2
  exact h2

private theorem isIdemAt_eq_or_mul_eq_zero {f : AE D} {Q : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f Q)
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : (Q = PP → f = e) ∧ (Q ≠ PP → f * e = 0) := by
  rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero hf.1 he.1 with rfl | h
  · refine ⟨fun _ => rfl, fun hne => ?_⟩
    exfalso
    obtain ⟨h1, hr1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D f Q hf
    have h0 := GlobalTheory.TameProd.resS_idem_eq_zero he (Ne.symm hne) h1
    rw [hr1] at h0
    exact one_ne_zero h0
  · refine ⟨fun hQ => ?_, fun _ => h⟩
    exfalso
    subst hQ
    obtain ⟨h1, hr1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D f Q hf
    obtain ⟨h2, hr2⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e Q he
    have h0 := resS_mul_eq_zero h1 h2 h Q hr1
    rw [hr2] at h0
    exact one_ne_zero h0

theorem idemSum_mul (ha : IsIdemSum a P) (hP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) : a * e = e := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := ha
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single PP]
  · rw [(isIdemAt_eq_or_mul_eq_zero (hes PP hP) he).1 rfl]
    exact he.1.1
  · intro Q hQ hne
    exact (isIdemAt_eq_or_mul_eq_zero (hes Q hQ) he).2 hne
  · intro h
    exact absurd hP h

private theorem exists_int_resS_eq_one_mul_idem_eq_zero_of_ne (ha : IsIdemSum a P) (hP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    {Q : Pl D.host.E} (hQ : Q ∈ P) (hne : PP ≠ Q) :
    ∃ z : AE D, ∃ hz : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      resS D.host.F Q ⟨_, hz⟩ = 1 ∧ z * (e + cA D e) = 0 := by
  have ha' := ha
  obtain ⟨⟨es, hes, -⟩, hac⟩ := ha
  obtain ⟨hz, hz1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q hQ)
  refine ⟨es Q, hz, hz1, ?_⟩
  have h1 : es Q * e = 0 := (isIdemAt_eq_or_mul_eq_zero (hes Q hQ) he).2 (Ne.symm hne)
  have h2 : es Q * a = es Q := by rw [mul_comm]; exact idemSum_mul ha' hQ (hes Q hQ)
  have h3 : a * e = e := idemSum_mul ha' hP he
  have h4 : cA D e = cA D a * cA D e := by rw [← map_mul, h3]
  rw [mul_add, h1, zero_add, h4, ← h2]
  calc es Q * a * (cA D a * cA D e) = (a * cA D a) * (es Q * cA D e) := by ring
    _ = 0 := by rw [hac, zero_mul]
set_option maxHeartbeats 1000000 in

theorem redFn_eq_one_of_ne (ha : IsIdemSum a P) (hP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) {V : HSp D}
    {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {g : GA D V} (hg : SuppAt e V g) (hβ : finE V g ∈ St β) {Q : Pl D.host.E}
    (hQ : Q ∈ P) (hne : PP ≠ Q) : redFn β Q (finE V g) = 1 := by
  obtain ⟨z, hz, hz1, hze⟩ := exists_int_resS_eq_one_mul_idem_eq_zero_of_ne ha hP he hQ hne
  have key : ∀ w : Formalism.L2.Herm.intAf D.host.F D.host.E,
      toEAf D z * (w : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) = 0 → resS D.host.F Q w = 0 := by
    intro w hw
    have h2 : (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * w = 0 := Subtype.ext hw
    have h3 := congrArg (resS D.host.F Q) h2
    rwa [map_mul, map_zero, hz1, one_mul] at h3
  have hX : ∀ i j, toEAf D (e + cA D e) * ((finE V g).val - 1) i j = ((finE V g).val - 1) i j := by
    intro i j
    rw [GlobalTheory.LatStab.finE_val]
    have h5 := congrArg (toEAf D) (hg i j)
    by_cases hij : i = j
    · subst hij
      simpa [Matrix.sub_apply, Matrix.map_apply] using h5
    · simpa [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply_ne hij] using h5
  rw [St, MonoidHom.mem_range] at hβ
  obtain ⟨y, hy⟩ := hβ
  have hfr : (frGL β y).val = β.val * (intGL D.host.F D.host.E V.rank y).val * (β⁻¹).val := by
    have h8 : frGL β y = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := rfl
    rw [h8, Units.val_mul, Units.val_mul]
  have hY : (intGL D.host.F D.host.E V.rank y).val = (β⁻¹).val * (finE V g).val * β.val := by
    rw [← hy, hfr]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hXz : toEAf D z • ((finE V g).val - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, ← hX i j, ← mul_assoc, ← map_mul, hze, map_zero, zero_mul, Matrix.zero_apply]
  have hYz : toEAf D z • ((intGL D.host.F D.host.E V.rank y).val - 1) = 0 := by
    have h6 : (intGL D.host.F D.host.E V.rank y).val - 1 = (β⁻¹).val * ((finE V g).val - 1) * β.val := by
      rw [hY, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
    rw [h6, ← Matrix.smul_mul, ← Matrix.mul_smul, hXz, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  apply Units.ext
  rw [Formalism.UG.P.bc_coe, Units.val_one]
  ext i j
  rw [Matrix.map_apply]
  have hw := congrFun (congrFun hYz i) j
  simp only [intGL, Formalism.UG.P.bc_coe, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hw
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have h7 := key ((y : Matrix (Fin V.rank) (Fin V.rank) _) i i - 1) (by simpa using hw)
    rwa [map_sub, map_one, sub_eq_zero] at h7
  · rw [Matrix.one_apply_ne hij]
    exact key _ (by simpa [Matrix.one_apply_ne hij] using hw)

end Idem

end GlobalTheory.DiagLiftFix

end
