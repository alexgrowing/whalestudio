import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix

variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']

theorem v_lt_one_iff_tendsto (p : HeightOneSpectrum (𝓞 F)) (y : p.adicCompletion F) :
    Valued.v y < 1 ↔ Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact (Valued.toNormedField.norm_lt_one_iff).symm

theorem v_map_lt_one_iff (p : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 F'))
    (c : p.adicCompletion F ≃+* q.adicCompletion F') (hc : Continuous c) (y : p.adicCompletion F) :
    Valued.v (c y) < 1 ↔ Valued.v y < 1 := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F' q
  have hc' : Continuous c.symm := GlobalTheory.SlocVal.continuous_symm c hc
  rw [v_lt_one_iff_tendsto, v_lt_one_iff_tendsto]
  constructor
  · intro h; simpa using GlobalTheory.SlocVal.tendsto_pow_map c.symm.toRingHom hc' h
  · intro h; simpa using GlobalTheory.SlocVal.tendsto_pow_map c.toRingHom hc h

theorem v_map_le_one_iff (p : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 F'))
    (c : p.adicCompletion F ≃+* q.adicCompletion F') (hc : Continuous c) (y : p.adicCompletion F) :
    Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have hcy : c y ≠ 0 := by simpa using hy
  rw [← not_lt, ← not_lt, Valuation.one_lt_val_iff _ hy, Valuation.one_lt_val_iff _ hcy, ← map_inv₀,
    v_map_lt_one_iff p q c hc]

section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc

theorem complRel_lt_one (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    ValuativeRel.valuation (p.adicCompletion F) x < 1 ↔ Valued.v x < 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem complRel_le_one (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    ValuativeRel.valuation (p.adicCompletion F) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

end GlobalTheory.TypeBlockFix

namespace GlobalTheory.TypeBlockFix
open ValuativeRel

theorem det_ne_zero_of_mem_blockGrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : GL (Fin (r + t)) k), h ∈ GlobalTheory.BlockType.blockGrp k r t → (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
  intro k _ _ _ _ r t h hh
  obtain ⟨⟨g, rfl⟩, hcol⟩ := hh
  set M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] := g.val.map (IsLocalRing.residue 𝒪[k]) with hM
  have hcolM : ∀ (a : Fin (r + t)) (j : Fin r), M a (Fin.castAdd t j) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a (Fin.castAdd t j) := by
    intro a j
    have h1 := hcol a j
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
        ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
      by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
    rw [e] at h1
    have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] :=
      (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1)
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub] at hm
    have : IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j)) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a (Fin.castAdd t j) := by
      by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
    rw [hM, Matrix.map_apply, ← this]
    exact sub_eq_zero.1 hm
  have hdetM : M.det ≠ 0 := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnits_det_units g).map _).ne_zero
  set M' := Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M with hM'
  have h21 : M'.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM', Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    rw [hcolM]
    exact Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this; omega)
  have h11 : M'.toBlocks₁₁ = 1 := by
    ext i j
    simp only [hM', Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left]
    rw [hcolM]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne (fun e' => e (Fin.castAdd_inj.1 e')), Matrix.one_apply_ne e]
  have hdet' : M.det = (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [← Matrix.det_reindex_self finSumFinEquiv.symm M, ← hM', ← Matrix.fromBlocks_toBlocks M', h21, h11,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rfl
  have hD : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
    intro h0
    apply hdetM
    rw [hdet', hM, show (g.val.map (IsLocalRing.residue 𝒪[k])).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      (IsLocalRing.residue 𝒪[k]).mapMatrix (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)) from rfl,
      ← RingHom.map_det, h0, map_zero]
  intro h0
  apply hD
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [RingHom.map_det]; rfl
  rw [e] at h0
  exact (FaithfulSMul.algebraMap_injective 𝒪[k] k) (h0.trans (map_zero _).symm)

end GlobalTheory.TypeBlockFix

namespace GlobalTheory.TypeBlockFix
open Filter Topology

theorem comp_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (χ : HChar L) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.IsCompAt χ s ξ → GlobalTheory.NPin.IsComp χ s.w μ → ∀ u, ξ u = μ (Units.map c.toRingHom.toMonoidHom u) := by
  intro L _ _ _ s χ ξ μ c hc hci hξ hμ
  let ψ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ := μ.comp (Units.map c.toRingHom.toMonoidHom)
  have hψ : ∀ u, ψ u = μ (Units.map c.toRingHom.toMonoidHom u) := fun u => rfl

  have hkξ : IsOpen (ξ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    obtain ⟨N, hN⟩ := hξ.1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield L) s.v
    set z : s.v.adicCompletion (maximalRealSubfield L) := (algebraMap _ _ π) ^ N with hz
    have hvz : Valued.v z = WithZero.exp (-(N : ℤ)) := by
      rw [hz, map_pow, adic_valued_algebraMap, hπ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvz; exact WithZero.zero_ne_coe hvz
    have hr0 : Valued.v.restrict z ≠ 0 := by
      rw [Ne, map_eq_zero]; exact hz0
    have hS : {y : s.v.adicCompletion (maximalRealSubfield L) | Valued.v (y - 1) < WithZero.exp (-(N : ℤ))} ∈
        𝓝 (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr0, fun y hy => ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hy
      rw [← hvz]; exact hy
    have := Units.continuous_val.continuousAt (x := (1 : (s.v.adicCompletion (maximalRealSubfield L))ˣ)) hS
    refine Filter.mem_of_superset this fun u hu => ?_
    exact hN u (le_of_lt hu)

  have hkψ : IsOpen (ψ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    have : (ψ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) =
        (Units.map c.toRingHom.toMonoidHom) ⁻¹' (μ.ker : Set (s.w.adicCompletion L)ˣ) := by
      ext u; simp [ψ]
    rw [this]
    exact hμ.1.preimage (Continuous.units_map _ hc)
  set H := MonoidHom.eqLocus ξ ψ with hH
  have hHo : IsOpen (H : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := ξ.ker ⊓ ψ.ker) ?_ (hkξ.inter hkψ)
    intro u hu
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    show ξ u = ψ u
    rw [hu.1, hu.2]

  have hagree : ∀ (a : maximalRealSubfield L) (ha : algebraMap _ (s.v.adicCompletion (maximalRealSubfield L)) a ≠ 0),
      Units.mk0 _ ha ∈ H := by
    intro a ha
    have hx : algebraMap (maximalRealSubfield L) L a ≠ 0 := by
      intro h0; apply ha
      rw [← s.i.commutes a, h0, map_zero]
    have e1 : Units.mk0 _ ha = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 _ hx) := by
      ext; simp
    have e2 : Units.map c.toRingHom.toMonoidHom (Units.mk0 _ ha) =
        Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 _ hx) := by
      ext; simp [← hci]
    show ξ _ = ψ _
    rw [hψ, e2, hμ.2, e1, hξ.2]
  intro u
  show u ∈ H
  have hSo : IsOpen {z : (s.v.adicCompletion (maximalRealSubfield L))ˣ | u⁻¹ * z ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_id)
  have hSu : {z : (s.v.adicCompletion (maximalRealSubfield L))ˣ | u⁻¹ * z ∈ H} ∈ 𝓝 u :=
    hSo.mem_nhds (by simp [H.one_mem])
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hSu
  obtain ⟨T, hT, hTS⟩ := hSu
  have hT' : T ∩ {x | x ≠ 0} ∈ 𝓝 (u : s.v.adicCompletion (maximalRealSubfield L)) :=
    Filter.inter_mem hT (isOpen_ne.mem_nhds u.ne_zero)
  obtain ⟨a, ha1, ha2⟩ := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).mem_nhds hT'
  have hw : u⁻¹ * Units.mk0 _ ha2 ∈ H := hTS ha1
  have := H.mul_mem hw (H.inv_mem (hagree a ha2))
  rw [mul_inv_cancel_right] at this
  simpa using H.inv_mem this

end GlobalTheory.TypeBlockFix

open GlobalTheory.TypeBlockFix in
theorem GlobalTheory.typeVec_blockChar_fixedPlace : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hsw _hT c hc hci Q
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i Q)
  rw [P.H.av.typeV] at hy
  have hfT : (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  refine ⟨(P.M.loc i).real y, hy, fun h0 => hy0 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)), ?_⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hLv⟩ := P.H.level.uni i j hj k v s hsw
  intro x hx hblk
  set G := s.loc D.R.nV x with hG
  set h := Matrix.GeneralLinearGroup.map c.toRingHom G with hh
  have hent : ∀ a b, h.val a b = c (G.val a b) := fun a b => rfl
  have hient : ∀ a b, (h⁻¹).val a b = c ((G⁻¹).val a b) := by
    intro a b; rw [hh, ← map_inv]; rfl
  have hle : ∀ y, ValuativeRel.valuation _ (c y) ≤ 1 → Valued.v y ≤ 1 := fun y hy' =>
    (v_map_le_one_iff _ _ c hc y).1 ((complRel_le_one _ _).1 hy')
  have hlt : ∀ y, ValuativeRel.valuation _ (c y) < 1 → Valued.v y < 1 := fun y hy' =>
    (v_map_lt_one_iff _ _ c hc y).1 ((complRel_lt_one _ _).1 hy')
  have hI : ∀ a b, Valued.v (G.val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hent]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO hblk.1 a b)
  have hI' : ∀ a b, Valued.v ((G⁻¹).val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hient]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO ((KO _ _).inv_mem hblk.1) a b)
  have hcol : ∀ a (b : Fin D.R.nV), b.val < D.R.r → a ≠ b → Valued.v (G.val a b) < 1 := by
    intro a b hb hab
    refine hlt _ ?_
    have := hblk.2 a ⟨b.val, hb⟩
    rw [← hent]
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) a b) < 1 at this
    rw [Matrix.one_apply_ne hab, sub_zero] at this
    exact this
  have hdiag : ∀ (b : Fin D.R.nV), b.val < D.R.r → Valued.v (G.val b b - 1) < 1 := by
    intro b hb
    refine hlt _ ?_
    have := hblk.2 b ⟨b.val, hb⟩
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val b b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) b b) < 1 at this
    rw [Matrix.one_apply_eq, hent] at this
    rwa [map_sub, map_one]
  have hpara : NG.ParaRT s D.R.r G := by
    refine ⟨mem_GLint_of_entries _ G (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI a b))
      (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI' a b)), ?_⟩
    · intro a b ha hb
      exact hcol a b hb (fun e => by rw [e] at ha; omega)
  have huni : NG.UniRT s D.R.r G := by
    refine ⟨hpara, fun a b ha hb => ⟨fun hab => hcol a b hb (fun e => by rw [e] at hab; omega), fun e => ?_⟩⟩
    subst e; exact hdiag a ha
  have hmem : x ∈ (P.M.loc i).J := (hLv.mem x hx).2 huni
  have hcdet : c (NG.detDD s D.R.r G) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {a : Fin D.R.nV // D.R.r ≤ a.val} :=
      { toFun := fun b => ⟨Fin.natAdd D.R.r b, by simp⟩
        invFun := fun a => ⟨a.1.val - D.R.r, by have h1 : a.1.val < D.R.r + D.R.t := a.1.2; omega⟩
        left_inv := fun b => by ext; simp
        right_inv := fun a => by ext; simp; have := a.2; omega }
    rw [NG.detDD, show c (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det =
      c.toRingHom (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det from rfl,
      RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  have hdet : NG.detDD s D.R.r G ≠ 0 := by
    intro h0
    exact (det_ne_zero_of_mem_blockGrp _ _ _ _ hblk) (hcdet.symm.trans (by rw [h0, map_zero]))
  refine (hfT.2 ⟨x, hmem⟩).trans ?_
  congr 1
  rw [hLv.chr x hmem hx (Units.mk0 _ hdet) rfl]
  have hsd : Valued.v (NG.supDiag s D.R.r G) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · exact hcol a b hab.2 (fun e => by rw [e] at hab; omega)
    · simp
  rw [hψ.1 _ hsd, one_mul, comp_agree _ s _ ξ _ c hc hci hξ (hS.mu i s.w hw j hj)]
  exact (GlobalTheory.BlockType.blockChar_eq _ _ _ hcdet).symm
