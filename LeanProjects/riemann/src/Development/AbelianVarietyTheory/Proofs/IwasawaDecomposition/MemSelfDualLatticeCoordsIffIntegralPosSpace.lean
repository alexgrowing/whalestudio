import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowLat

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

abbrev swi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F ⊗[F] E :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm.toAlgHom.toRingHom

theorem swi_sw (z : FiniteAdeleRing (𝓞 F) F ⊗[F] E) : swi F E (sw F E z) = z :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm_apply_apply z

theorem swi_tmul (a : FiniteAdeleRing (𝓞 F) F) (x : E) : swi F E (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := by
  show (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x
  rw [AlgEquiv.symm_apply_eq]; rfl

theorem mem_stdLat_iff {m : ℕ} (y : Fin m → E) :
    y ∈ Formalism.L2.Col.stdLat E m ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem intAf_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := fun v => ha v

theorem intAd_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => ha v

variable {n m : ℕ} (e : Fin n ≃ Fin m) (L : Set (Fin n → E))

theorem latHat_to_latS (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (w : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hw : w ∈ Formalism.MainNotions.StandardLattice.latHat F E L) :
    (fun j => sw F E (w (e.symm j))) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m) := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hmem : (1 : E) ⊗ₜ[F] a ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) :=
      Subring.subset_closure (Or.inr ⟨⟨a, intAf_mem ha⟩, rfl⟩)
    have hx' : (fun j => x (e.symm j)) ∈ Formalism.L2.Col.stdLat E m := (mem_stdLat_iff _).2 fun j => (hL x).1 hx _
    have h2 : (fun j => sw F E (a ⊗ₜ[F] x (e.symm j))) =
        (⟨_, hmem⟩ : Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) •
          (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) := by
      funext j
      show x (e.symm j) ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x (e.symm j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx', rfl⟩)
  | zero =>
    have : (fun j => sw F E ((0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (e.symm j))) = 0 := by
      funext j; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun j => sw F E ((y + z) (e.symm j))) = (fun j => sw F E (y (e.symm j))) + (fun j => sw F E (z (e.symm j))) := by
      funext j; simp
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : (fun j => sw F E ((-y) (e.symm j))) = -(fun j => sw F E (y (e.symm j))) := by
      funext j; simp
    rw [this]; exact neg_mem hy

theorem mul_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∀ w ∈ Formalism.MainNotions.StandardLattice.latHat F E L, (fun i => swi F E s * w i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hs using Subring.closure_induction with
  | mem s hs =>
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rcases hs with ⟨⟨c, hc⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
      · obtain ⟨o, rfl⟩ := RingHom.mem_range.1 hc
        apply AddSubgroup.subset_closure
        refine ⟨a, ha, fun i => algebraMap (𝓞 E) E o * x i, (hL _).2 fun i => ?_, ?_⟩
        · obtain ⟨p, hp⟩ := (hL x).1 hx i
          exact ⟨o * p, by rw [map_mul, hp]⟩
        · funext i
          show swi F E (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (a ⊗ₜ[F] x i) =
            a ⊗ₜ[F] (algebraMap (𝓞 E) E o * x i)
          rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      · apply AddSubgroup.subset_closure
        refine ⟨b * a, intAd_mem (mul_mem hb (intAf_mem ha)), x, hx, ?_⟩
        funext i
        show swi F E ((1 : E) ⊗ₜ[F] b) * (a ⊗ₜ[F] x i) = (b * a) ⊗ₜ[F] x i
        rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero =>
      have : (fun i => swi F E s * (0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) i) = 0 := by
        funext i; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun i => swi F E s * (y + z) i) = (fun i => swi F E s * y i) + (fun i => swi F E s * z i) := by
        funext i; simp [mul_add]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun i => swi F E s * (-y) i) = -(fun i => swi F E s * y i) := by
        funext i; simp
      rw [this]; exact neg_mem hy
  | zero =>
    intro w _
    have : (fun i => swi F E 0 * w i) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | one =>
    intro w hw
    have : (fun i => swi F E 1 * w i) = w := by funext i; simp
    rw [this]; exact hw
  | add s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s + t) * w i) = (fun i => swi F E s * w i) + (fun i => swi F E t * w i) := by
      funext i; simp [add_mul]
    rw [this]; exact add_mem (hs w hw) (ht w hw)
  | neg s _ hs =>
    intro w hw
    have : (fun i => swi F E (-s) * w i) = -(fun i => swi F E s * w i) := by
      funext i; simp
    rw [this]; exact neg_mem (hs w hw)
  | mul s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s * t) * w i) = (fun i => swi F E s * (fun i => swi F E t * w i) i) := by
      funext i; simp [mul_assoc]
    rw [this]; exact hs _ (ht w hw)

theorem latS_to_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hv : v ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)) :
    (fun i => swi F E (v (e i))) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨1, intAd_mem (one_mem _), fun i => x (e i), (hL _).2 fun i => (mem_stdLat_iff x).1 hx _, ?_⟩
    funext i
    show swi F E (x (e i) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x (e i)
    exact swi_tmul _ _
  | zero =>
    have : (fun i => swi F E ((0 : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (e i))) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => swi F E ((y + z) (e i))) = (fun i => swi F E (y (e i))) + (fun i => swi F E (z (e i))) := by
      funext i; simp
    rw [this]; exact add_mem hy hz
  | smul s y _ hy =>
    have : (fun i => swi F E ((s • y) (e i))) = (fun i => swi F E (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (fun i => swi F E (y (e i))) i) := by
      funext i
      show swi F E ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * y (e i)) = _
      rw [map_mul]
    rw [this]; exact mul_latHat L hL _ s.2 _ hy

theorem mem_iff_swap (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E))
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (x : Fin n → E) :
    ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L ↔
      (fun j => x (e.symm j)) ∈ Formalism.UG.CS.globLat
        (Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g)) (Formalism.L2.Col.stdLat E m) := by
  set w := ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) with hw
  have hv : (((Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g))⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).mulVec
        (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) = fun j => sw F E (w (e.symm j)) := by
    rw [← map_inv, ← map_inv]
    funext j
    rw [hw]
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Formalism.UG.inclE]
  show w ∈ _ ↔ _ ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)
  rw [hv]
  constructor
  · exact latHat_to_latS e L hL w
  · intro h
    have := latS_to_latHat e L hL _ h
    simpa [swi_sw] using this

end Gen

theorem mem_selfDualLatticeCoords_iff_integral_posSpace (D : D7) (W : HSpace D.host.E) (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (hW : W = Formalism.BasicNotions.Examples₂.posSpace hstar N) (x : Fin W.rank → D.host.E) :
    x ∈ L0c D W ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  subst hW
  revert x
  show ∀ x : Fin N → D.host.E, (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) ∈ Formalism.BasicNotions.Examples₂.stdLat N ↔
    ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)
  intro x
  have hsum : (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) = x := by
    simpa only [Pi.basisFun_repr] using (Pi.basisFun D.host.E (Fin N)).sum_repr x
  rw [hsum, Formalism.BasicNotions.Examples₂.stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    have e1 : (∑ j, c j • (Pi.basisFun D.host.E (Fin N)) j) i = c i • (1 : D.host.E) := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.basisFun_apply]
      · intro b _ hb
        simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
      · simp
    rw [← congrFun hc i, e1, Algebra.smul_def, mul_one]
  · intro hx
    choose c hc using hx
    refine ⟨c, ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply, Algebra.smul_def, hc]
    · intro b _ hb
      simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
    · simp

theorem mem_selfDualLatticeCoords_iff_integral_rowSpace (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok)
    (x : Fin X.toD7.sp.X'.rank → X.toD7.host.E) :
    x ∈ L0c X.toD7 X.toD7.sp.X' ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 X.toD7.host.E) X.toD7.host.E) := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  exact mem_selfDualLatticeCoords_iff_integral_posSpace X.toD7 X.toD7.sp.X' hs _ h2 x

theorem hLat_eq_decoAd_N : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), X.B.fields.Ok → I.Ok →
    ∀ (U : Set I.ι) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X'),
      Bridge.hLat X.toD7.sp.X' h = ((RowAd.decoAd X I t h).1.N).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap := by
  intro X px I _ hI U t h
  have hN : (RowAd.decoAd X I t h).1.N = Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _) := by
    unfold RowAd.decoAd Formalism.L2.Col.decoOf
    split_ifs with h1
    · rfl
    · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (RowDeco.ptE_mem_UAd X I hI h)) h1
  rw [hN]
  unfold Bridge.hLat
  conv_rhs => rw [← Submodule.span_eq ((Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _)).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap)]
  congr 1
  ext x
  exact (mem_iff_swap (finCongr (RowAd.rank_X' X)) (L0c X.toD7 X.toD7.sp.X') (mem_selfDualLatticeCoords_iff_integral_rowSpace X I hI) h.1 x).trans
    (Submodule.mem_map_equiv (e := LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm) _).symm

end GlobalTheory.Mem.R3.RowLat
