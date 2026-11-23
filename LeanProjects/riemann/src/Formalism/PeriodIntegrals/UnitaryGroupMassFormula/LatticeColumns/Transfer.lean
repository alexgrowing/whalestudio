import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH PI.MassDataKppVolLemmas
open scoped TensorProduct
open Matrix

theorem card_dc_congr {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (Γ K : Subgroup G) (Γ' K' : Subgroup G')
    (hΓ : Γ.map φ.toMonoidHom = Γ') (hK : K.map φ.toMonoidHom = K') :
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (Γ' : Set G') (K' : Set G')) := by
  classical
  have himg : ∀ a : G, φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) =
      DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G') := by
    intro a
    subst hΓ hK
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
      exact DoubleCoset.mem_doubleCoset.2 ⟨φ h, ⟨h, hh, rfl⟩, φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩
    · intro hy
      obtain ⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
      exact ⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩
  refine Nat.card_congr (Quotient.congr φ.toEquiv fun a b => ?_)
  show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b (Γ : Set G) (K : Set G) ↔
    DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G') =
      DoubleCoset.doubleCoset (φ b) (Γ' : Set G') (K' : Set G')
  rw [← himg, ← himg]
  exact (Set.image_injective.2 φ.injective).eq_iff.symm

def tfE (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) : I.Gf ≃* HA (Af I.F) I.cm.sig I.J :=
  MulEquiv.ofBijective (tfHom I hb) ⟨Bridge_tf_injective I hb, Bridge_tf_surjective I hb⟩

theorem tfE_apply (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (x : I.Gf) : tfE I hb x = tf I hb x := rfl

theorem ratV_eq_swap (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) :
    ratV (F := I.F) (Af I.F) w = fun i => swapE I (Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
  funext i
  simp [ratV, swapE, Formalism.UG.inclE, inclR]

theorem lin_tf_fix_iff (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (x : I.Gf) (w : Fin I.n → I.E) :
    lin (Af I.F) I.cm.sig I.J (tf I hb x) (ratV (F := I.F) (Af I.F) w) = ratV (F := I.F) (Af I.F) w ↔
      I.fmat x *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
  have hm := Bridge_mat I hb x
  simp only [lin, Matrix.mulVecLin_apply]
  rw [hm, ratV_eq_swap]
  have key : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      (I.fmat x).map (swapE I) *ᵥ (fun i => swapE I (v i)) = fun i => swapE I ((I.fmat x *ᵥ v) i) := by
    intro v
    funext i
    exact (RingHom.map_mulVec (swapE I : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E) (I.fmat x) v i).symm
  rw [key]
  constructor
  · intro h
    funext i
    exact (swapE I).injective (congrFun h i)
  · intro h
    rw [h]

theorem mem_Hfin_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (x : X.B.I.Gf) :
    x ∈ PoincareSetting.Hfin X u ↔ tf X.B.I hb x ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  unfold Hsub
  rw [mem_stabT]
  simp only [lin_tf_fix_iff]
  show (∀ y ∈ PoincareSetting.fixSet X u, X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I y =
    Formalism.L2.SG.HidaSetting.incl X.B.I y) ↔ _
  constructor
  · intro h b
    refine Fin.addCases (fun i => ?_) (fun j => ?_) b
    · rw [tupH, Fin.append_left]
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rw [F0, Fin.snoc_last]
        exact h _ (Or.inr rfl)
      · rw [F0, Fin.snoc_castSucc]
        exact h _ (Or.inl (Or.inl ⟨k, rfl⟩))
    · rw [tupH, Fin.append_right]
      exact h _ (Or.inl (Or.inr ⟨j, rfl⟩))
  · intro h y hy
    rcases hy with ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hz)
    · have := h (Fin.castAdd D.R.rS (Fin.castSucc a))
      rw [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at this
      exact this
    · have := h (Fin.natAdd (D.R.rS + 1) a)
      rw [tupH, Fin.append_right] at this
      exact this
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      have := h (Fin.castAdd D.R.rS (Fin.last D.R.rS))
      rw [tupH, Fin.append_left, F0, Fin.snoc_last] at this
      exact this

theorem map_Hfin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    (PoincareSetting.Hfin X u).map (tfE X.B.I hb).toMonoidHom =
      Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_Hfin_iff X hb u x).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := Bridge_tf_surjective X.B.I hb y
    exact ⟨x, (mem_Hfin_iff X hb u x).2 hy, rfl⟩

def hE {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    ↥(PoincareSetting.Hfin X u) ≃* ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  ((tfE X.B.I hb).subgroupMap (PoincareSetting.Hfin X u)).trans (MulEquiv.subgroupCongr (map_Hfin X hb u))

theorem hE_val {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (h : PoincareSetting.Hfin X u) :
    ((hE X hb u h : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) =
      tf X.B.I hb (h : X.B.I.Gf) := rfl

theorem coe_K2Hg {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = Subtype.val ⁻¹' K2u X hb u := by
  unfold unitaryLevelClosureSubgroup
  have : (Subtype.val ⁻¹' K2u X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
      (unitaryLevelIntersection X hb hK u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := rfl
  rw [this, Subgroup.closure_eq]

theorem mem_conjugate_level_finite_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (x : X.B.I.Gf) :
    tf X.B.I hb x ∈ K2u X hb u ↔ (X.xu u)⁻¹ * x * X.xu u ∈ X.K2 := by
  rw [mem_conjugate_level_iff]
  constructor
  · rintro ⟨k, hk, e⟩
    have e' : tfE X.B.I hb (X.xu u * k * (X.xu u)⁻¹) = tfE X.B.I hb x := by
      rw [map_mul, map_mul, map_inv]
      exact e
    have := (tfE X.B.I hb).injective e'
    rw [← this]
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    have : finHA X hb (X.xu u) * finHA X hb ((X.xu u)⁻¹ * x * X.xu u) * (finHA X hb (X.xu u))⁻¹ =
        tfE X.B.I hb (X.xu u * ((X.xu u)⁻¹ * x * X.xu u) * (X.xu u)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [this]
    simp [mul_assoc, tfE_apply]

theorem map_Ku {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    (PoincareSetting.Ku X u hK).map (hE X hb u).toMonoidHom = unitaryLevelClosureSubgroup X hb u := by
  ext y
  rw [Subgroup.mem_map]
  have hy : y ∈ unitaryLevelClosureSubgroup X hb u ↔ (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
    rw [← SetLike.mem_coe, coe_K2Hg X hb hK u]
    rfl
  rw [hy]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hE_val, mem_conjugate_level_finite_iff]
    exact hh
  · intro h2
    obtain ⟨h, rfl⟩ := (hE X hb u).surjective y
    refine ⟨h, ?_, rfl⟩
    rw [hE_val, mem_conjugate_level_finite_iff] at h2
    exact h2

theorem fin_mat (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (γ : I.GA) :
    ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb γ)).2) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) _) = (I.fmat γ.2).map (swapE I) := by
  have hB := (toHA_isBridge I hb γ).2
  rw [hB]
  ext i j
  simp only [ofHAFin, Matrix.map_apply]
  rw [← Bridge_tens_eq]
  rfl

theorem inclR_comp_sig {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) : (inclR (F := F) R).comp (σ : E →+* E) = (sigR R σ).comp (inclR (F := F) R) := by
  exact RingHom.ext fun e => by simp [inclR, sigR]

theorem map_iotaF {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (hGF : AdBridgeGF X.B.I) :
    (PoincareSetting.iotaF X u).range.map (hE X hb u).toMonoidHom = GamHA X u := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, ⟨γ, rfl⟩, rfl⟩
    obtain ⟨M, hM, -, hf⟩ := (Subgroup.mem_inf.1 γ.2).1
    show (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (tf X.B.I hb (γ : X.B.I.GA).2) : GL (Fin X.B.I.n) _) ∈
      HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J
    refine ⟨M, hM, ?_⟩
    apply Units.ext
    show (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (Af X.B.I.F)) = _
    rw [Bridge_mat, hf, Matrix.map_map]
    congr 1
  · intro hy
    have hy' : (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :
        GL (Fin X.B.I.n) _) ∈ HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := hy
    obtain ⟨M, hM, hMy⟩ := Subgroup.mem_map.1 hy'
    let Hf : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J :=
      ⟨Formalism.UG.bc (inclR (F := X.B.I.F) (AF X.B.I.F)) M,
        Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sig (AF X.B.I.F) X.B.I.cm.sig) _ M hM⟩
    have hrat : Hf ∈ ratHA X.B.I := ⟨M, hM, rfl⟩
    rw [← hGF (toHA X.B.I hb) (toHA_isBridge X.B.I hb)] at hrat
    obtain ⟨γ, hγ, hγe⟩ := hrat
    have htf : tf X.B.I hb γ.2 = (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
      apply Bridge_HA_ext
      rw [Bridge_mat, ← fin_mat X.B.I hb γ, hγe]
      rw [← hMy]
      show ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (AF X.B.I.F))).map
        (tensMap (E := X.B.I.E) (sndA X.B.I.F)) = (M : Matrix _ _ _).map (inclR (F := X.B.I.F) (Af X.B.I.F))
      rw [Matrix.map_map]
      congr 1
    have hγ2 : γ.2 ∈ PoincareSetting.Hfin X u := (mem_Hfin_iff X hb u γ.2).2 (htf ▸ y.2)
    obtain ⟨M', hM', hinf, hfin⟩ := hγ
    have hγ1 : γ.1 ∈ PoincareSetting.Hinf X u := by
      intro v x hx
      have hfix : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
        have h0 := hγ2 x hx
        rw [hfin] at h0
        funext i
        have := PIW.AdelClassFin.DictRing.nontrivial (F := X.B.I.F)
        apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
        have h1 := congrFun h0 i
        have h2 := RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F))
          (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i
        exact h2.trans h1
      have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))
      rw [hinf v]
      simp only [rv]
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      congr 1
      funext i
      have h3 := RingHom.map_mulVec (X.B.I.φ v) (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i
      rw [hfix] at h3
      exact h3.symm
    refine ⟨⟨γ.2, hγ2⟩, ⟨⟨γ, Subgroup.mem_inf.2 ⟨⟨M', hM', hinf, hfin⟩, Subgroup.mem_prod.2 ⟨hγ1, hγ2⟩⟩⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    exact htf

theorem class_sets_equal_card : ClassBijStep := by
  intro D X hb hK u hGF _hL
  exact card_dc_congr (hE X hb u) _ _ _ _ (map_iotaF X hb u hGF) (map_Ku X hb hK u)

theorem stabilizers_trivial_of_neat : HAStabTrivStep := by
  intro D X hb hK u hGF _hL hn x'
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  rw [← map_iotaF X hb u hGF] at hy1
  obtain ⟨h, ⟨γ, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hy1
  obtain ⟨k', hk', hke⟩ := Subgroup.mem_map.1 hy2
  rw [← map_Ku X hb hK u] at hk'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  obtain ⟨x, rfl⟩ := (hE X hb u).surjective x'
  have e : PoincareSetting.iotaF X u γ = x * k * x⁻¹ := by
    apply (hE X hb u).injective
    rw [map_mul, map_mul, map_inv]
    exact hke.symm
  have h1 : x⁻¹ * PoincareSetting.iotaF X u γ * x ∈ PoincareSetting.Ku X u hK := by
    rw [e]
    simpa [mul_assoc] using hk
  have h2 := hn x γ h1
  rw [Subgroup.mem_bot, h2]
  simp

end PIW.MassDataColumns
