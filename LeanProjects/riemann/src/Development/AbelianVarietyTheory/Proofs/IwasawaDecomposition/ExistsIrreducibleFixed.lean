import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsBorelSphRevInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip
open GlobalTheory.Mem.Chr hiding HChar

namespace GlobalTheory.CuspRep.ParLaws

section Group

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isIrreducible_comp {π : Representation ℂ G V} (h : π.IsIrreducible) (ψ : G' →* G)
    (hψ : Function.Surjective ψ) : Representation.IsIrreducible (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨h0, h1⟩ := (isIrreducible_iff π).1 h
  refine (isIrreducible_iff _).2 ⟨h0, fun U hU => h1 U fun g v hv => ?_⟩
  obtain ⟨g, rfl⟩ := hψ g
  exact hU g v hv

theorem isSubquotient_comp {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π)
    (ψ : G' →* G) : IsSubquotient (σ.comp ψ : Representation ℂ G' W) (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

theorem exists_irreducible_fixed (ρ : Representation ℂ G V) (K : Subgroup G) (hK : fixed ρ K ≠ ⊥) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ G Y),
      σ.IsIrreducible ∧ fixed σ K ≠ ⊥ ∧ IsSubquotient σ ρ := by
  obtain ⟨v, hf, hv⟩ := (Submodule.ne_bot_iff _).1 hK
  let R := MonoidAlgebra ℂ G
  let v' : ρ.asModule := v
  let S : Submodule R ρ.asModule := Submodule.span R {v'}
  have hS : v' ∈ S := Submodule.mem_span_singleton_self v'
  have hne : (⊥ : Submodule R S) ≠ ⊤ := by
    intro h
    have : (⟨v', hS⟩ : S) ∈ (⊥ : Submodule R S) := by
      rw [h]; trivial
    exact hv (congrArg Subtype.val ((Submodule.mem_bot R).1 this))
  obtain ⟨T, hT, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R S)).resolve_left hne
  have h1 : (S.mapIic T).1 ⋖ S := (covBy_iff_coatom_Iic (S.mapIic T).2).2 ((S.mapIic.isCoatom_iff T).2 hT)
  let φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  refine ⟨_, _, _, subQuot (φ.symm S) (φ.symm (S.mapIic T).1), isIrreducible_subQuot ((apply_covBy_apply_iff φ.symm).2 h1),
    (Submodule.ne_bot_iff _).2 ⟨Submodule.Quotient.mk ⟨v, hS⟩, fun x => ?_, fun h => h1.lt.not_ge ?_⟩,
    φ.symm S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩
  · rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact congrArg Submodule.Quotient.mk (Subtype.ext ((hf x).trans (one_smul _ _)))
  · have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
    exact (Submodule.span_singleton_le_iff_mem _ _).2 h2

theorem exists_fun (P K : Subgroup G) (χ : P →* ℂˣ) (hG : ∀ g, ∃ p : P, ∃ x ∈ K, g = p * x)
    (hχ : ∀ p : P, p.1 ∈ K → χ p = 1) :
    ∃ φ : G → ℂ, φ 1 = 1 ∧ (∀ (p : P) g, φ (p * g) = χ p * φ g) ∧ ∀ g, ∀ x ∈ K, φ (g * x) = φ g := by
  choose b x hx e using hG
  have key : ∀ (p : P), ∀ y ∈ K, χ (b (p * y)) = χ p := fun p y hy => by
    have h1 : ((p⁻¹ * b (p * y) : P) : G) = y * (x (p * y))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, Subgroup.coe_mul, mul_assoc, ← e, Subgroup.coe_inv, inv_mul_cancel_left]
    have h2 := hχ _ (h1 ▸ mul_mem hy (inv_mem (hx _)))
    rwa [map_mul, map_inv, inv_mul_eq_one, eq_comm] at h2
  refine ⟨fun g => χ (b g), ?_, fun p g => ?_, fun g y hy => ?_⟩
  · simpa using congrArg Units.val (key 1 1 (one_mem _))
  · have := key (p * b g) _ (hx g)
    rw [Subgroup.coe_mul, mul_assoc, ← e] at this
    simp only [this, map_mul, Units.val_mul]
  · have := key (b g) _ (mul_mem (hx g) hy)
    rw [← mul_assoc, ← e] at this
    simp only [this]

end Group

section Local

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def diagU (b : borel k (Fin n)) (i : Fin n) : kˣ := GeneralLinearGroup.det (leviProj k (points (Fin n)) b i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_diagU (b : borel k (Fin n)) (i : Fin n) : (diagU b i : k) = b.1.val i i := by
  rw [diagU, GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  rfl

variable (k) in

def borelChar (α : Fin n → ℂˣ) : borel k (Fin n) →* ℂˣ :=
  (deltaHalf k (fun _ : Fin n => Unit) * (torusChar fun i => SmGL.unrChar k (α i)).comp
    (leviTorus k (Fin n)).symm.toMonoidHom).comp (leviProj k (points (Fin n)))

theorem borelChar_apply (α : Fin n → ℂˣ) (b : borel k (Fin n)) : borelChar k α b =
    ∏ i : Fin n, absPow k ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2) (diagU b i) * α i ^ ord k (diagU b i) := by
  rw [Finset.prod_mul_distrib]
  refine congrArg₂ (· * ·) ((deltaHalf_apply k _).trans (Finset.prod_congr rfl fun i _ => ?_)) (torusChar_apply _ _)
  rw [modExp_fin _ (fun _ => by simp)]
  rfl

theorem law_iff (α : Fin n → ℂˣ) (φ : GL (Fin n) k → ℂ) :
    φ ∈ indSpace (parab k (points (Fin n))) ((twist ((ofChar (torusChar fun i => SmGL.unrChar k (α i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom) (deltaHalf k fun _ : Fin n => Unit)).comp (leviProj k (points (Fin n)))) ↔
    ∀ (b : borel k (Fin n)) g, φ (b * g) = borelChar k α b * φ g :=
  forall₂_congr fun b g => Iff.of_eq (congrArg (φ (b * g) = ·) (mul_assoc _ _ _).symm)

theorem borelChar_eq_one (α : Fin n → ℂˣ) (b : borel k (Fin n)) (hb : b.1 ∈ KO k (Fin n)) : borelChar k α b = 1 := by
  rw [borelChar_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hb
  have h3 := congrArg (valuation k) (inv_diag_mul b.2 i)
  rw [map_mul, map_one] at h3
  have a1 : valuation k (b.1.val i i) ≤ 1 := h1 i i
  have a2 : valuation k ((b.1⁻¹).val i i) ≤ 1 := h2 i i
  have h : valuation k (diagU b i : k) = 1 := by
    rw [val_diagU]
    exact le_antisymm a1 (h3.ge.trans (mul_le_of_le_one_left' a2))
  rw [isUnram_absPow k _ _ h, ord_eq_zero h, zpow_zero, mul_one]

theorem exists_hasSatake (α : Fin n → ℂˣ) : ∃ π : IrrRep (GL (Fin n) k), HasSatake π.ρ α := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_fun (borel k (Fin n)) (KO k (Fin n)) (borelChar k α) (fun g => by
    obtain ⟨b, hb, x, hx, e⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    exact ⟨⟨b, (mem_borel _).2 hb⟩, x, hx, e⟩) (borelChar_eq_one α)
  obtain ⟨f, hf, e⟩ := (SphCompletion.exists_fixed_iff (fun i => SmGL.unrChar k (α i)) φ).2
    ⟨(law_iff α φ).2 h2, fun x hx g => h3 g x hx⟩
  have h0 : f ≠ 0 := fun h => one_ne_zero (by rw [← h1, ← e, h]; rfl)
  obtain ⟨Y, _, _, σ, a1, a2, a3⟩ := exists_irreducible_fixed _ _ ((Submodule.ne_bot_iff _).2 ⟨f, hf, h0⟩)
  exact ⟨⟨Y, σ, a3.isSmooth (isSmooth_parInd _ _), a1⟩, a1, a2, a3⟩

def flip (j : k' →+* k) (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k := invRevT.comp (GeneralLinearGroup.map j)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [IsNonarchimedeanLocalField k'] in

theorem continuous_flip {j : k' →+* k} (hj : Continuous j) : Continuous (flip j n) :=
  Units.continuous_iff.2 ⟨continuous_matrix fun a b => hj.comp (Units.continuous_coe_inv.matrix_elem b.rev a.rev),
    continuous_matrix fun a b => hj.comp (Units.continuous_val.matrix_elem b.rev a.rev)⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [IsNonarchimedeanLocalField k']
  [TopologicalSpace k] [TopologicalSpace k'] in

theorem flip_surjective {j : k' →+* k} (hj : Function.Surjective j) : Function.Surjective (flip j n) := fun g => by
  let e := RingEquiv.ofBijective j ⟨j.injective, hj⟩
  refine ⟨GeneralLinearGroup.map e.symm.toRingHom (invRevT g), ?_⟩
  conv_rhs => rw [← invRevT_invRevT g]
  exact congrArg invRevT (Units.ext (Matrix.ext fun a b => e.apply_symm_apply _))

theorem hasSatake_flip {j : k' →+* k} (hc : Continuous j) (hj : Function.Surjective j)
    (hv : ∀ x, valuation k' x ≤ 1 → valuation k (j x) ≤ 1)
    (ho : ∀ x, ord k (Units.map j.toMonoidHom x) = ord k' x) (hq : resCard k = resCard k')
    {π : Representation ℂ (GL (Fin n) k) V} {α : Fin n → ℂˣ} (h : HasSatake π α) :
    HasSatake (π.comp (flip j n) : Representation ℂ (GL (Fin n) k') V) fun i => (α i.rev)⁻¹ := by
  have hB : ∀ b : borel k' (Fin n), flip j n b ∈ borel k (Fin n) := fun b =>
    invRevT_mem_borel ((mem_borel _).2 fun a c h => (congrArg j ((mem_borel _).1 b.2 a c h)).trans (map_zero j))
  have hχ : ∀ b : borel k' (Fin n), borelChar k α ⟨_, hB b⟩ = borelChar k' (fun i => (α i.rev)⁻¹) b := fun b => by
    rw [borelChar_apply, borelChar_apply]
    refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
    have e : diagU ⟨_, hB b⟩ i = (Units.map j.toMonoidHom (diagU b i.rev))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      change (diagU ⟨_, hB b⟩ i : k) * j (diagU b i.rev : k') = 1
      rw [val_diagU, val_diagU, ← map_one j, ← inv_diag_mul b.2 i.rev, map_mul]
      rfl
    rw [e, ord_inv_eq_neg, ho, Fin.revPerm_apply, Fin.rev_rev, _root_.zpow_neg, _root_.inv_zpow, map_inv]
    congr 1
    have e2 : ((((n : ℤ) - 1 - 2 * ((i.rev : Fin n) : ℕ) : ℤ) : ℂ) / 2) = -((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2) := by
      rw [← neg_div, ← Int.cast_neg]
      have := i.2
      rw [Fin.val_rev]
      congr 2
      omega
    rw [e2, absPow_neg, MonoidHom.inv_apply, _root_.inv_inj]
    ext
    rw [val_absPow, val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, ho, hq]
  refine ⟨isIrreducible_comp h.1 _ (flip_surjective hj), ?_, (isSubquotient_comp h.2.2 _).trans ?_⟩
  · obtain ⟨v, h1, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun x => h1 ⟨flip j n x, invRevT_mem_KO ?_⟩, h0⟩
    obtain ⟨a1, a2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 x.2
    exact (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun a b => hv _ (a1 a b), fun a b => hv _ (a2 a b)⟩
  · refine .of_injective ⟨⟨⟨fun f => ⟨⟨f.1.1 ∘ flip j n, (law_iff _ _).2 fun b g => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((IsOpen.preimage (continuous_flip hc) f.2).mem_nhds ?_)
        fun g hg => Subtype.ext (funext fun x => ?_))⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun g => ?_⟩ fun f f' e => ?_
    · rw [← hχ, Function.comp_apply, map_mul]
      exact (law_iff α _).1 f.1.2 ⟨_, hB b⟩ _
    · change ind _ _ (flip j n 1) f.1 = f.1
      rw [map_one, map_one]
      rfl
    · exact (congrArg f.1.1 (map_mul (flip j n) x g)).trans (congrFun (congrArg Subtype.val hg) _)
    · exact LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => (congrArg f.1.1 (map_mul (flip j n) x g)).symm))
    · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      obtain ⟨x, rfl⟩ := flip_surjective hj x
      exact congrFun (congrArg (fun z => z.1.1) e) x

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def toRep {G : Type} [Group G] [TopologicalSpace G] (σ : SmIrr G) : IrrRep G := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩

def toCl {G : Type} [Group G] [TopologicalSpace G] (σ : Irr G) : IrrCl G :=
  Quotient.map (sa := SmIrr.setoid G) (sb := IrrRep.setoid G) toRep (fun _ _ h => h) σ

section Par

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}

def locRec (hL : GlobalTheory.Published.LocalLanglandsGL) (h : IsPlaceOver A w) : IrrGL (w.adicCompletion E) → WD h :=
  (hL.1 E Ω A w h).exists.choose

theorem isRec_locRec (hL : GlobalTheory.Published.LocalLanglandsGL) (h : IsPlaceOver A w) : IsRec h (locRec hL h) :=
  (hL.1 E Ω A w h).exists.choose_spec

variable {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem unr_iff (H : IsRec h rc) (σ : IrrRep (GL (Fin a) (w.adicCompletion E))) :
    (rc (cls σ)).unr ↔ IsSpherical σ.ρ := by
  obtain ⟨_, _, _, -, H⟩ := H
  rw [← H.sph]
  exact ⟨fixed_ne_bot_of_equiv (equivRep σ).symm, fixed_ne_bot_of_equiv (equivRep σ)⟩

theorem rec_eq_diag (H : IsRec h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ}
    (hα : HasSatake σ.ρ α) : rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨_, _, _, -, H⟩ := H
  have φ := equivRep σ
  exact H.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩

theorem exists_hasSatake_of_unr (H : IsRec h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))}
    (hu : (rc (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨m, c, e⟩ := Unram.exists_diag hu
  have H' := H
  obtain ⟨_, _, _, -, H'⟩ := H'
  obtain rfl : a = m := by simpa [e] using (H'.dim (cls σ)).symm
  obtain ⟨τ, hτ⟩ := exists_hasSatake (k := w.adicCompletion E) fun i => (c i)⁻¹
  have e2 := rec_eq_diag H hτ
  simp only [inv_inv] at e2
  obtain ⟨φ⟩ := (H'.eq_iff τ σ).1 (e2.trans e.symm)
  exact ⟨_, σ.irr, fixed_ne_bot_of_equiv φ hτ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hτ.2.2⟩

variable [IsTotallyComplex E]

def locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (π : CG E a) (h : IsPlaceOver A w) : WD h :=
  locRec hL h ⟨a, toCl (π.loc w)⟩

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)

theorem locPar_mk {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ)
    (h : IsPlaceOver A w) : locPar hL (CG.mk π) h = locRec hL h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locPar, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem lpDim_locPar (π : CG E a) (h : IsPlaceOver A w) : (locPar hL π h).lpDim = a := by
  obtain ⟨_, _, _, -, H⟩ := isRec_locRec hL h
  exact H.dim _

include hF in

theorem eventually_unr (π : CG E a) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (locPar hL π h).unr := by
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  refine (locPar_mk hL hσ h).symm ▸ (unr_iff (isRec_locRec hL h) _).2 ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm

theorem isSmoothChar_loc (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) : IsSmoothChar (χ.loc w) := by
  have h2 : Continuous (GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (CuspSub.locDet 1 χ w).comp (GeneralLinearGroup.scalar (Fin 1)) = χ.loc w :=
    MonoidHom.ext fun z => congrArg (χ.loc w) (CG.det_oneByOne z)
  exact h3 ▸ IsSmoothChar.comp (CuspSub.isOpen_ker_locDet χ w) _ h2

theorem locPar_ofChar (χ : HChar E) (h : IsPlaceOver A w) :
    locPar hL (CG.ofChar χ) h = locRec hL h (.ofChar (χ.loc w) (isSmoothChar_loc χ w)) :=
  locPar_mk hL (CG.isLoc_ofChar χ w) h

include hF in

theorem locPar_twist (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w) :
    locPar hL (π.twist χ) h = (locPar hL π h).lpChar (locPar hL (CG.ofChar χ) h) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, _, -, H⟩ := isRec_locRec hL h
  refine (locPar_mk hL (hσ.twist χ) h).trans ?_
  rw [locPar_ofChar, show locPar hL (Quotient.mk _ π) h = _ from locPar_mk hL hσ h, ← H.twist]
  exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

include hF in

theorem locPar_tw (π : CG E a) (χ : CG E 1) (h : IsPlaceOver A w) :
    locPar hL (π.tw χ) h = (locPar hL π h).lpChar (locPar hL χ h) := by
  rw [CG.tw, locPar_twist hL hF, CG.ofChar_toChar]

theorem hasInfChar_infChar (π : CG E a) (τ : E →+* ℂ) : π.HasInfChar τ (π.infChar τ) :=
  hasInfChar_infChar_of_commute E a (fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X) π τ

theorem infChar_tw (π : CG E a) (χ : CG E 1) (τ : E →+* ℂ) (s : ℂ) (hs : χ.infChar τ = {s}) :
    (π.tw χ).infChar τ = (π.infChar τ).map (· + s) := by
  rw [← CG.ofChar_toChar χ, CG.infChar_ofChar, Multiset.singleton_inj] at hs
  exact hs ▸ ((hasInfChar_infChar π τ).twist _).infChar_eq

end Par

section Conj

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_thetaGL {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (p : R →+* T) (c : R →+* R) (q : R →+* S)
    (j : S →+* T) (h : ∀ x, p (c x) = j (q x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (thetaGL a c g) =
      PhiU a T * invT a T (GeneralLinearGroup.map j (GeneralLinearGroup.map q g)) * (PhiU a T)⁻¹ := by
  have e : GeneralLinearGroup.map p (PhiU a R) = PhiU a T := Units.ext (Matrix.ext fun i k => by
    change p (GlobalTheory.Tw.Phi a R i k) = GlobalTheory.Tw.Phi a T i k
    simp [GlobalTheory.Tw.Phi, apply_ite p])
  change GeneralLinearGroup.map p (PhiU a R * invT a R (GeneralLinearGroup.map c g) * (PhiU a R)⁻¹) = _
  rw [map_mul, map_mul, map_inv, e]
  exact congrArg (fun x => PhiU a T * x * (PhiU a T)⁻¹) (Units.ext (Matrix.ext fun i k => h _))

theorem invRevT_eq {R : Type} [CommRing R] (g : GL (Fin a) R) :
    invT a R g = longElt a R * invRevT g * (longElt a R)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  refine Units.ext (Matrix.ext fun i k => ?_)
  change ∑ l, (g⁻¹).val l i * (if k = l.rev then 1 else 0) = ∑ l, (if l = i.rev then 1 else 0) * (g⁻¹).val k.rev l.rev
  rw [Finset.sum_eq_single k.rev (fun b _ hb => by rw [if_neg (fun e => hb (by rw [e, Fin.rev_rev])), mul_zero]) (by simp),
    Finset.sum_eq_single i.rev (fun b _ hb => by rw [if_neg hb, zero_mul]) (by simp)]
  simp

theorem thetaGL_locGL (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) ((conjSrc c w).adicCompletion E)) :
    thetaGL a (conjFin c) (locGL E a (conjSrc c w) g) =
      locGL E a w (PhiU a _ * longElt a _ * flip (conjLoc c w) a g * (PhiU a _ * longElt a _)⁻¹) := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (thetaGL a (conjFin c) (locGL E a (conjSrc c w) g)) =
      GeneralLinearGroup.map (pLoc E v)
        (locGL E a w (PhiU a _ * longElt a _ * flip (conjLoc c w) a g * (PhiU a _ * longElt a _)⁻¹)) := fun v => by
    rw [map_thetaGL _ _ _ _ (fun x => pLoc_conjFin c x v)]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, pLoc_locGL, invRevT_eq, _root_.mul_inv_rev]
      simp only [mul_assoc]
      rfl
    · rw [pLoc_locGL_of_ne hv, pLoc_locGL_of_ne fun e => hv (conjSrc_injective c e), map_one, map_one, mul_one,
        mul_inv_cancel]
  exact Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i k) (key v))

theorem conjLoc_surjective (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) : Function.Surjective (conjLoc c w) := by
  obtain ⟨t, t1, t2, -⟩ := exists_finCompl_map c.symm ((conjPl_symm_iff c _ _).2 (conjPl_conjSrc c w))
  refine fun x => ⟨t x, ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => conjLoc c w (t x) = x) x
    (isClosed_eq ((conjLoc_spec c w).1.comp t1) continuous_id) fun y => ?_
  rw [t2, (conjLoc_spec c w).2.1, c.apply_symm_apply]

theorem valuation_le_one_iff (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem hasSatake_flip_conjLoc (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {α : Fin a → ℂˣ} (h : HasSatake π α) :
    HasSatake (π.comp (flip (conjLoc c w) a) : Representation ℂ _ V) fun i => (α i.rev)⁻¹ :=
  hasSatake_flip (conjLoc_spec c w).1 (conjLoc_surjective c w)
    (fun x hx => by rwa [valuation_le_one_iff, (conjLoc_spec c w).2.2, ← valuation_le_one_iff])
    (fun x => by
      rw [SphCompletion.ord_completion, SphCompletion.ord_completion]
      exact congrArg (fun z => -WithZero.log z) ((conjLoc_spec c w).2.2 x))
    (by rw [resCard_eq_normV, resCard_eq_normV, GlobalTheory.AntiLAdic.normV_conjPl (conjPl_conjSrc c w)]) h

variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

theorem isLocComp_flip {π : CuspSub L a} (hπ : π.IsCsd) {w : HeightOneSpectrum (𝓞 L)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion L))} (hσ : π.IsLocComp w σ) :
    π.IsLocComp (conjSrc (IsCMField.complexConj L).toRingEquiv w)
      ⟨σ.V, σ.ρ.comp (flip (conjLoc (IsCMField.complexConj L).toRingEquiv w) a),
        isSmooth_comp σ.smooth _ (continuous_flip (conjLoc_spec _ w).1),
        isIrreducible_comp σ.irred _ (flip_surjective (conjLoc_surjective _ w))⟩ := by
  obtain ⟨T, hT⟩ := hπ
  obtain ⟨f, h0, hf⟩ := hσ
  refine ⟨T.toLinearMap ∘ₗ f ∘ₗ σ.ρ (PhiU a _ * longElt a _), fun h => h0 (LinearMap.ext fun v => T.injective ?_),
    fun g v => ?_⟩
  · have := LinearMap.congr_fun h (σ.ρ (PhiU a _ * longElt a _)⁻¹ v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
    rw [LinearMap.zero_apply, map_zero]
    exact this
  · change T (f (σ.ρ _ (σ.ρ (flip _ a g) v))) = π.op (.fin _) (T (f (σ.ρ _ v)))
    rw [← hT, thetaOp, thetaGL_locGL, ← CuspSub.locRep_eq, ← hf, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem csd_unr (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (π : CG L a) (hπ : π.IsCsd)
    {w w' : HeightOneSpectrum (𝓞 L)} (hc : ConjPl (IsCMField.complexConj L).toRingEquiv w w')
    {A A' : ValuationSubring Ω} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (hu : (locPar hL π h).unr) :
    (locPar hL π h').unr ∧ (locPar hL π h').frobEig = (locPar hL π h).frobEig.map (·⁻¹) := by
  obtain rfl : w' = conjSrc (IsCMField.complexConj L).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hc (IsCMField.complexConj L x)).symm
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF L a π w
  have e : locPar hL (Quotient.mk _ π) h = _ := locPar_mk hL hσ h
  have e' : locPar hL (Quotient.mk _ π) h' = _ := locPar_mk hL (isLocComp_flip hπ hσ) h'
  rw [e] at hu
  obtain ⟨α, hα⟩ := exists_hasSatake_of_unr (isRec_locRec hL h) hu
  rw [e, e', rec_eq_diag (isRec_locRec hL h) hα, rec_eq_diag (isRec_locRec hL h') (hasSatake_flip_conjLoc _ w hα),
    WD.frobEig_diag, WD.frobEig_diag, Multiset.map_map]
  refine ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), ?_⟩
  conv_rhs => rw [← Finset.map_univ_equiv Fin.revPerm, Finset.map_val, Multiset.map_map]
  simp

end Conj

def jumps (a : ℕ) (m : Multiset ℂ) : Multiset ℤ := m.map fun z => ⌊(-z + ((a : ℂ) - 1) / 2).re⌋

theorem map_jumps {a : ℕ} {m : Multiset ℂ} (h : ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    (jumps a m).map (fun n : ℤ => (n : ℂ)) = m.map fun z => -z + ((a : ℂ) - 1) / 2 := by
  rw [jumps, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  have e : -((n : ℂ) + ((a : ℂ) - 1) / 2) + ((a : ℂ) - 1) / 2 = ((-n : ℤ) : ℂ) := by push_cast; ring
  rw [Function.comp_apply, e, Complex.intCast_re, Int.floor_intCast]

theorem map_jumps_iff {a : ℕ} {m : Multiset ℂ} (J : Multiset ℤ) :
    J.map (fun n : ℤ => (n : ℂ)) = m.map (fun z => -z + ((a : ℂ) - 1) / 2) ↔
      (∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) ∧ J = jumps a m := by
  refine ⟨fun e => ?_, fun ⟨h, e⟩ => e ▸ map_jumps h⟩
  have h : ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 := fun z hz => by
    obtain ⟨n, -, hn⟩ := Multiset.mem_map.1 (e ▸ Multiset.mem_map_of_mem (fun z => -z + ((a : ℂ) - 1) / 2) hz)
    exact ⟨-n, by push_cast; linear_combination hn⟩
  exact ⟨h, Multiset.map_injective Int.cast_injective (e.trans (map_jumps h).symm)⟩

example : jumps 2 {1 / 2, -1 / 2} = {0, 1} :=
  (((map_jumps_iff (a := 2) {0, 1}).1 (by norm_num)).2).symm

def jumpsInf {E Q : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field Q] (ι : Q ≃+* ℂ) {a : ℕ} (π : CGu E a)
    (τ : E →+* Q) : Multiset ℤ := jumps a (π.infChar (ι.toRingHom.comp τ))

def jumpsWt {E Q : Type} [Field E] [Field Q] (ι : Q ≃+* ℂ) (n : ℕ) (wt : (E →+* ℂ) → Multiset ℂ) (τ : E →+* Q) :
    Multiset ℤ := jumps n (wt (ι.toRingHom.comp τ))

section Host

open Formalism.BasicNotions

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locG (hL : GlobalTheory.Published.LocalLanglandsGL) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) :
    WD (pl.2 w) :=
  haveI := host_isCMField H; locPar hL π.1 (pl.2 w)

theorem laws (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {R : Ranks}
    (H : Formalism.BasicNotions.Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (pl : Formalism.GaloisCohomology.Places H.E Ω) :
    haveI := host_isCMField H
    (∀ {a} (π : HostCGu H a) w, (locG hL pl π w).lpDim = a) ∧
    (∀ {a} (π : HostCGu H a), ∀ᶠ w in Filter.cofinite, (locG hL pl π w).unr) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) w,
      locG hL pl (π.tw χ) w = (locG hL pl π w).lpChar (locG hL pl χ w)) ∧
    (∀ {a} (π : HostCGu H a) τ, Multiset.card (π.infChar τ) = a) ∧
    (∀ {a} (π : HostCGu H a), π.IsRegAlg ↔ ∀ τ, (π.infChar τ).Nodup ∧
      ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) τ (s : ℂ), χ.infChar τ = {s} →
      (π.tw χ).infChar τ = (π.infChar τ).map (· + s)) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1), χ.IsCsd → π.IsCsd → (π.tw χ).IsCsd) ∧
    (∀ {a} (π : HostCGu H a) w w', π.IsCsd → IsConjPl H w w' → (locG hL pl π w).unr →
      (locG hL pl π w').unr ∧ (locG hL pl π w').frobEig = (locG hL pl π w).frobEig.map (·⁻¹)) ∧
    (∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) {a} (π : HostCGu H a) (τ : H.E →+* Q), π.IsRegAlg →
      (jumpsInf ι π τ).map (fun n : ℤ => (n : ℂ)) =
        (π.infChar (ι.toRingHom.comp τ)).map fun z => -z + ((a : ℂ) - 1) / 2) ∧
    ∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) (n : ℕ) (wt : (H.E →+* ℂ) → Multiset ℂ) (τ : H.E →+* Q),
      ((jumpsWt ι n wt τ).map (fun n : ℤ => (n : ℂ)) =
        (wt (ι.toRingHom.comp τ)).map fun z => -z + ((n : ℂ) - 1) / 2) ↔
      ∀ z ∈ wt (ι.toRingHom.comp τ), ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  have := host_isCMField H
  refine ⟨fun π w => lpDim_locPar hL π.1 _, fun π => (eventually_unr (Ω := Ω) hL hF π.1).mono fun w hw => hw _ _,
    fun π χ w => locPar_tw hL hF π.1 χ.1 _, fun π τ => π.1.card_infChar τ, fun π => CG.isRegAlg_iff π.1,
    fun π χ τ s => infChar_tw π.1 χ.1 τ s, fun π χ hχ hπ => CG.IsCsd.twist (χ.ofChar_equivChar.symm ▸ hχ) hπ,
    fun π w w' hπ hc => csd_unr hL hF π.1 hπ ((conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (host_complexConj H _))) _ _,
    fun Q _ ι a π τ h => map_jumps (h _).2, fun Q _ ι n wt τ => ⟨fun h => ((map_jumps_iff _).1 h).1, map_jumps⟩⟩

end Host

end GlobalTheory.CuspRep.ParLaws
