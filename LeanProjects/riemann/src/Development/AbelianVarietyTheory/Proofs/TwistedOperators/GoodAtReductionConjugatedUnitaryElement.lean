import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Matrix

namespace GlobalTheory.RedFrame

open Formalism.L2.SG.Pf.RowDictPf

theorem tauF_gen (I : Formalism.MainNotions.S.AutInst) (z : TensorProduct I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.E) :
    Formalism.L2.SG.AdBridge.tauF I z = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.E
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Formalism.L2.SG.AdBridge.tauF, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

theorem finE_iota_symm (D : D7) (k : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) :
    (finE (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm (1, k))).1 =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat k := by
  have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (1, k)).2
  rw [hb]
  ext i j
  exact (tauF_gen (Formalism.IndefR.RationalEmbedding.inst D) _).symm

theorem Lv_eq (D : D7) : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
  show Formalism.L2.SG.InstExistsPf.Lv D = _
  ext x
  constructor
  · intro hx
    refine ⟨(Formalism.L2.SG.InstExistsPf.crdE D) x, hx, ?_⟩
    show (VS D).frame.equivFun ((VS D).frame.equivFun.symm x) = x
    exact LinearEquiv.apply_symm_apply _ _
  · rintro ⟨y, hy, rfl⟩
    show (VS D).frame.equivFun.symm ((VS D).frame.equivFun y) ∈ (VS D).L0
    exact (congrArg (· ∈ (VS D).L0) (LinearEquiv.symm_apply_apply (VS D).frame.equivFun y)).mpr hy

open Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin in

theorem core (I : Formalism.MainNotions.S.AutInst) (w : HeightOneSpectrum (𝓞 I.E)) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) (hβ : IsFrame (F := I.F) β I.L)
    (x : I.Gf) (hx : x ∈ I.Kset) (iso : ZMod p ≃+* kP w) (m : ℕ) (hm : m = I.n) :
    RedMat0 I w p x (Matrix.of fun i j : Fin m =>
      iso.symm (((redFn (F := I.F) β w (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) :
        GL (Fin I.n) (kP w)) : Matrix (Fin I.n) (Fin I.n) (kP w)) (Fin.cast hm i) (Fin.cast hm j))) := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ u, u ∈ Formalism.L2.Herm.hatL (F := I.F) I.L ↔ u ∈ I.Lf := by
    intro u
    have e : ((fun x i => Formalism.UG.inclE (F := I.F) (Formalism.L2.Herm.Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) =
        Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) := by
      ext v; simp
    show u ∈ Submodule.span _ _ ↔ u ∈ Submodule.span _ _
    rw [e]
  have hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  have hxi : ∀ v, v ∈ I.Lf ↔ (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := (Formalism.UG.stabGL I.Lf).inv_mem hx
  have hS : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) ∈ St β :=
    (GlobalTheory.LevSplit.mem_St_iff β I.L hβ _).2 ⟨fun v hv => (hL _).2 ((hx' _).1 ((hL _).1 hv)),
      fun v hv => (hL _).2 ((hxi _).1 ((hL _).1 hv))⟩
  obtain ⟨y, hy⟩ := hS
  rw [← hy, redFn_frGL]
  set col : Fin I.n → (Fin I.n → I.E ⊗[I.F] Af I.F) := fun j => β.1 *ᵥ Pi.single j 1 with hcol_def
  have hβsum : ∀ v, β.1 *ᵥ v = ∑ j, v j • col j := by
    intro v
    funext k
    simp [col, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, mul_comm]
  have hcol : ∀ j, col j ∈ I.Lf := by
    intro j
    refine (hL _).1 ((hβ _).2 fun k => ?_)
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hfm : I.fmat x = β.1 * (intGL I.F I.E I.n y).1 * (β⁻¹).1 := by
    show ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) = _
    rw [← hy]; rfl
  have hact : ∀ i, I.fmat x *ᵥ col i = ∑ j, ((y.1 j i : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col j := by
    intro i
    rw [hfm, ← hβsum]
    simp only [col, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rfl
  have hres : ∀ c : Formalism.L2.Herm.intAf I.F I.E, resS I.F w c = 0 → ∀ u ∈ I.Lf,
      (c : I.E ⊗[I.F] Af I.F) • u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro c hc
    have hc' : c ∈ Submodule.span (Formalism.L2.Herm.intAf I.F I.E) ((oToS I.F I.E) '' (w.asIdeal : Set (𝓞 I.E))) := by
      have h1 : ((RingEquiv.ofBijective (cmpS I.F w.asIdeal) (cmpS_bij (F := I.F) w.asIdeal w.ne_bot)).symm
        (Ideal.Quotient.mk (idS I.F w.asIdeal) c)) = 0 := hc
      have h2 := (map_eq_zero_iff _ (RingEquiv.injective _)).1 h1
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    refine Submodule.span_induction (p := fun (c : Formalism.L2.Herm.intAf I.F I.E) _ => ∀ u ∈ I.Lf,
      ((c : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • u ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨a, ha, rfl⟩ u hu
      exact smul_mem I w ha hu
    · intro u _; simp
    · intro a b _ _ ha hb u hu
      rw [AddMemClass.coe_add, add_smul]; exact add_mem (ha u hu) (hb u hu)
    · intro s a _ ha u hu
      rw [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
      exact Submodule.smul_mem _ s (ha u hu)
  choose b hbL hb using fun i => dense I w hp hcard (hcol i)
  refine ⟨b, ⟨hbL, ?_⟩, ?_⟩
  · intro z hz
    have hd : ∀ i, ((β⁻¹).1 *ᵥ iv I z) i ∈ Formalism.L2.Herm.intAf I.F I.E :=
      (hβ _).1 ((hL _).2 (DictLat.iv_mem I hz))
    choose c hc using fun i => int_surj I w hp hcard (resS I.F w ⟨_, hd i⟩)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e1 : iv I z = ∑ i, ((β⁻¹).1 *ᵥ iv I z) i • col i := by
      rw [← hβsum, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 : iv I z - ∑ i, (c i : I.E ⊗[I.F] Af I.F) • iv I (b i) =
        ∑ i, ((⟨_, hd i⟩ - (c i : Formalism.L2.Herm.intAf I.F I.E) : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col i +
          ∑ i, (c i : I.E ⊗[I.F] Af I.F) • (col i - iv I (b i)) := by
      conv_lhs => rw [e1]
      simp only [AddSubgroupClass.coe_sub, SubringClass.coe_intCast, sub_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e2]
    refine add_mem (Submodule.sum_mem _ fun i _ => hres _ ?_ _ (hcol i))
      (Submodule.sum_mem _ fun i _ => ?_)
    · rw [map_sub, ← hc i, map_intCast, sub_self]
    · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem (hb i) _
  · intro i
    show I.fmat x *ᵥ iv I (b i) - ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (b j) ∈ lamAf (F := I.F) (wLat0 I w)
    have hv : ∀ j, resS I.F w (y.1 j i - (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) :
        Formalism.L2.Herm.intAf I.F I.E)) = 0 := by
      intro j
      rw [map_sub, map_natCast, ← map_natCast iso, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply, sub_self]
    have key : I.fmat x *ᵥ iv I (b i) - ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        iv I (b j) = (∑ j, ((y.1 j i - (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) :
          Formalism.L2.Herm.intAf I.F I.E) : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col j +
          ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) • (col j - iv I (b j))) -
          I.fmat x *ᵥ (col i - iv I (b i)) := by
      rw [Matrix.mulVec_sub, hact i]
      simp only [AddSubgroupClass.coe_sub, SubringClass.coe_natCast, sub_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [key]
    exact sub_mem (add_mem (Submodule.sum_mem _ fun j _ => hres _ (hv j) _ (hcol j))
      (Submodule.sum_mem _ fun j _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb j) _))
      (stab_w I w hx (hb i))

theorem redFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (a β X : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn β PP (a⁻¹ * X * a) = redFn (a * β) PP X := by
  have e : ∀ y, frGL (a * β) y = a * frGL β y * a⁻¹ := by
    intro y
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  by_cases hX : X ∈ St (a * β)
  · obtain ⟨y, rfl⟩ := hX
    have : a⁻¹ * frGL (a * β) y * a = frGL β y := by rw [e]; group
    rw [this, redFn_frGL, redFn_frGL]
  · have h2 : a⁻¹ * X * a ∉ St β := by
      rintro ⟨y, hy⟩
      apply hX
      refine ⟨y, ?_⟩
      rw [e, hy]; group
    unfold redFn ext1
    rw [dif_neg h2, dif_neg hX]

theorem upperLeftBlock_eq_submatrix_of_rank_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) =
      (g : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  refine upper_block_val_submatrix hr fun i j hij => ?_
  exfalso
  have hi : blk2 (n := n) r i = 0 := by
    unfold blk2; rw [if_pos (lt_of_lt_of_le i.2 hn)]
  rw [hi] at hij
  exact Nat.not_lt_zero _ hij

theorem hw_eq {D : D7} (ιE : (Formalism.L2.SG.InstExistsPf.instOf D).E ≃+* D.host.E) (hid : ∀ x, ιE x = x)
    (w' : HeightOneSpectrum (𝓞 (Formalism.L2.SG.InstExistsPf.instOf D).E)) (PP : Pl D.host.E)
    (hw' : ∀ a : 𝓞 (Formalism.L2.SG.InstExistsPf.instOf D).E, a ∈ w'.asIdeal ↔ RingOfIntegers.mapRingEquiv ιE a ∈ PP.asIdeal) :
    w' = PP := by
  ext a
  rw [hw' a]
  have : RingOfIntegers.mapRingEquiv ιE a = a := RingOfIntegers.ext (by simp [hid] <;> rfl)
  rw [this]
  exact Iff.rfl

def finPt (D : D7) (k : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) : GL (Fin (Yc D 0).rank) (EAf D) := k.1

theorem glue (D : D7) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hιE : ∀ x, HEq (ιE x) x) (w' : HeightOneSpectrum (𝓞 I.E)) (PP : Pl D.host.E)
    (hw' : ∀ a : 𝓞 I.E, a ∈ w'.asIdeal ↔ RingOfIntegers.mapRingEquiv ιE a ∈ PP.asIdeal)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (kP PP) = p) (iso : ZMod p ≃+* kP PP)
    (t : GA D (D.sp.Y 0)) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hFr : IsFrame (finE (Yc D 0) t * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (k : I.Gf) (hk : k ∈ I.Kset) (hr : D.R.r ≤ (Yc D 0).rank) (hn : I.n = D.R.r) :
    RedMat0 I w' p k (Matrix.of fun i j : Fin D.R.r => iso.symm (((redFn β PP (finE (Yc D 0)
      (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm (1, k) * t)) : GL (Fin (Yc D 0).rank) (kP PP)) :
        Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP PP)) (Fin.castLE hr i) (Fin.castLE hr j))) := by
  subst h
  have hid : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  obtain rfl := hw_eq ιE hid w' PP hw'
  have hk1 : finE (Yc D 0) (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _))).symm (1, k) * t) =
      (finE (Yc D 0) t)⁻¹ * finPt D k * finE (Yc D 0) t := by
    show finE (D.sp.Y 0) (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _))).symm (1, k) * t) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext (finE_iota_symm D k)
  rw [hk1]
  have hc := redFn_conj (finE (Yc D 0) t) β (finPt D k) w'
  have hL : IsFrame (F := (Formalism.L2.SG.InstExistsPf.instOf D).F) (finE (Yc D 0) t * β) (Formalism.L2.SG.InstExistsPf.instOf D).L := by
    rw [Lv_eq]; exact hFr
  have := core (Formalism.L2.SG.InstExistsPf.instOf D) w' hp hcard (finE (Yc D 0) t * β) hL k hk iso D.R.r hn.symm
  refine (congrArg (RedMat0 (Formalism.L2.SG.InstExistsPf.instOf D) w' p k) ?_).mp this
  ext i j
  simp only [Matrix.of_apply]
  exact congrArg (fun g : GL (Fin (Yc D 0).rank) (kP w') =>
    iso.symm ((g : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP w')) (Fin.castLE hr i) (Fin.castLE hr j))) hc.symm

open Formalism.L2.SG.Pf.RowDictPf in

theorem goodAt_kap_red : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, GoodAt X k (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t hιE hpin _ _ _ hFrame k hk kv
  obtain ⟨plg, iso, hplw, -, -, hpe⟩ := hpin
  have hcomp : ∀ (x : G0 R.Pg D.R.r),
      ((cG x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) =
        ((x (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)).map
          (iso kv).symm := by
    intro x
    obtain ⟨g, rfl⟩ := R.eG.surjective x
    rw [hpe g kv]
    ext i j
    simp [Formalism.UG.bc]
  refine (congrArg (RedMat X (D.naut.plGw kv.1 kv.2) (D.host.g kv.1) k)
    (hcomp (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))).mpr ?_
  rw [← hplw kv, redMat_iff]
  have hr := (R.dat0 R.triv).hr
  have hrank : (Yc D 0).rank ≤ D.R.r := by
    have e : X.B.I.n = D.R.r := X.n_eq
    rw [h] at e
    exact e.le
  have hcard : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
    rw [hplw kv]; exact card_res_host kv.1 kv.2
  have G := glue D X.B.I h X.ιE hιE (wB X (plg kv).1) (plg kv).1 (fun a => Iff.rfl) (D.host.g_prime kv.1) hcard
    (iso kv) t (R.βY 0) hFrame k hk hr X.n_eq
  refine (congrArg (RedMat0 X.B.I (wB X (plg kv).1) (D.host.g kv.1) k) ?_).mp G
  ext i j
  simp only [Matrix.of_apply, Matrix.map_apply]
  congr 1
  exact (congrFun (congrFun (upperLeftBlock_eq_submatrix_of_rank_eq hr hrank _) i) j).symm

end GlobalTheory.RedFrame
