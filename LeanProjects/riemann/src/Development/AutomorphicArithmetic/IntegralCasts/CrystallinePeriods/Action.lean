import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

@[reducible] def actionOf {G B : Type*} [Monoid G] [CommRing B] (f : G → B →+* B)
    (h1 : ∀ x, f 1 x = x) (hmul : ∀ g h x, f (g * h) x = f g (f h x)) : MulSemiringAction G B where
  smul g x := f g x
  one_smul := h1
  mul_smul := hmul
  smul_zero g := map_zero (f g)
  smul_add g := map_add (f g)
  smul_one g := map_one (f g)
  smul_mul g := map_mul (f g)

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem toRingHom_one : MulSemiringAction.toRingHom G R 1 = RingHom.id R := by ext; simp

theorem toRingHom_mul (g h : G) : MulSemiringAction.toRingHom G R (g * h) =
    (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) := by
  ext; simp [mul_smul]

theorem toRingHom_injective (g : G) : Function.Injective (MulSemiringAction.toRingHom G R g) :=
  MulAction.injective g

variable [Fact ¬IsUnit (p : R)]

instance Tilt.mulSemiringAction : MulSemiringAction G (Tilt p R) :=
  actionOf (fun g => Tilt.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using Tilt.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (Tilt.map_map _ _ x).symm)

theorem Tilt.smul_def (g : G) (x : Tilt p R) :
    g • x = Tilt.map p (MulSemiringAction.toRingHom G R g) x := rfl

instance Ainf.mulSemiringAction : MulSemiringAction G (Ainf p R) :=
  actionOf (fun g => Ainf.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using Ainf.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (Ainf.map_map _ _ x).symm)

theorem Ainf.smul_def (g : G) (x : Ainf p R) :
    g • x = Ainf.map p (MulSemiringAction.toRingHom G R g) x := rfl

instance AinfInv.mulSemiringAction : MulSemiringAction G (AinfInv p R) :=
  actionOf (fun g => AinfInv.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using AinfInv.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (AinfInv.map_map _ _ x).symm)

theorem AinfInv.smul_def (g : G) (x : AinfInv p R) :
    g • x = AinfInv.map p (MulSemiringAction.toRingHom G R g) x := rfl

variable [IsAdicComplete (span {(p : R)}) R]

instance BdRPlus.mulSemiringAction : MulSemiringAction G (BdRPlus p R) :=
  actionOf (fun g => BdRPlus.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using BdRPlus.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (BdRPlus.map_map _ _ x).symm)

theorem BdRPlus.smul_def (g : G) (x : BdRPlus p R) :
    g • x = BdRPlus.map p (MulSemiringAction.toRingHom G R g) x := rfl

instance Acris.mulSemiringAction : MulSemiringAction G (Acris p R) :=
  actionOf (fun g => Acris.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using Acris.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (Acris.map_map _ _ x).symm)

theorem Acris.smul_def (g : G) (x : Acris p R) :
    g • x = Acris.map p (MulSemiringAction.toRingHom G R g) x := rfl

instance BcrisPlus.mulSemiringAction : MulSemiringAction G (BcrisPlus p R) :=
  actionOf (fun g => BcrisPlus.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using BcrisPlus.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (BcrisPlus.map_map _ _ x).symm)

theorem BcrisPlus.smul_def (g : G) (x : BcrisPlus p R) :
    g • x = BcrisPlus.map p (MulSemiringAction.toRingHom G R g) x := rfl

instance Bcris.mulSemiringAction : MulSemiringAction G (Bcris p R) :=
  actionOf (fun g => Bcris.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g))
    (fun x => by
      rw [Bcris.map_congr _ Function.injective_id toRingHom_one, Bcris.map_id])
    (fun g h x => by
      have hi := (toRingHom_injective (R := R) g).comp (toRingHom_injective h)
      rw [Bcris.map_map _ _ _ _ hi, Bcris.map_congr _ hi (toRingHom_mul g h)])

theorem Bcris.smul_def (g : G) (x : Bcris p R) :
    g • x = Bcris.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g) x := rfl

instance Bst.mulSemiringAction : MulSemiringAction G (Bst p R) :=
  actionOf (fun g => Bst.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g))
    (fun x => by
      rw [Bst.map_congr _ Function.injective_id toRingHom_one, Bst.map_id])
    (fun g h x => by
      have hi := (toRingHom_injective (R := R) g).comp (toRingHom_injective h)
      rw [Bst.map_map _ _ _ _ hi, Bst.map_congr _ hi (toRingHom_mul g h)])

theorem Bst.smul_def (g : G) (x : Bst p R) :
    g • x = Bst.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g) x := rfl

instance BdR.mulSemiringAction : MulSemiringAction G (BdR p R) :=
  actionOf (fun g => (BdR.map p (MulSemiringAction.toRingEquiv G R g)).toRingHom)
    (fun x => by
      have : MulSemiringAction.toRingEquiv G R 1 = RingEquiv.refl R := by ext; simp
      simp [this])
    (fun g h x => by
      have : MulSemiringAction.toRingEquiv G R (g * h) =
          (MulSemiringAction.toRingEquiv G R h).trans (MulSemiringAction.toRingEquiv G R g) := by
        ext; simp [mul_smul]
      simp [this, BdR.map_map])

theorem BdR.smul_def (g : G) (x : BdR p R) :
    g • x = BdR.map p (MulSemiringAction.toRingEquiv G R g) x := rfl

instance tateModule.smul : SMul G (tateModule p R) :=
  ⟨fun g η => tateModule.map p (MulSemiringAction.toRingHom G R g) η⟩

instance PFlat.smul : SMul G (PFlat p R) :=
  ⟨fun g ϖ => PFlat.map p (MulSemiringAction.toRingHom G R g) ϖ⟩

theorem tateModule.coe_smul (g : G) (η : tateModule p R) : (g • η).1 = g • η.1 := rfl
theorem PFlat.coe_smul (g : G) (ϖ : PFlat p R) : (g • ϖ).1 = g • ϖ.1 := rfl

theorem Tilt.untilt_smul (g : G) (x : Tilt p R) :
    PreTilt.untilt (g • x) = g • PreTilt.untilt x := Tilt.untilt_map _ x

omit [IsAdicComplete (span {(p : R)}) R] in
theorem Ainf.smul_teich (g : G) (x : Tilt p R) : g • Ainf.teich p x = Ainf.teich p (g • x) :=
  Ainf.map_teich _ x

theorem Ainf.theta_smul (g : G) (x : Ainf p R) : Ainf.theta p R (g • x) = g • Ainf.theta p R x :=
  Ainf.theta_map _ x

theorem BdRPlus.theta_smul (g : G) (x : BdRPlus p R) : BdRPlus.theta p R (g • x) =
    awayMap p (MulSemiringAction.toRingHom G R g) (BdRPlus.theta p R x) := BdRPlus.theta_map _ x

omit [IsAdicComplete (span {(p : R)}) R] in
theorem AinfInv.smul_algebraMap (g : G) (x : Ainf p R) :
    g • algebraMap _ (AinfInv p R) x = algebraMap _ _ (g • x) := AinfInv.map_algebraMap _ x
theorem BdRPlus.smul_algebraMap (g : G) (x : AinfInv p R) :
    g • algebraMap _ (BdRPlus p R) x = algebraMap _ _ (g • x) := BdRPlus.map_algebraMap _ x
theorem BdRPlus.smul_algebraMap_ainf (g : G) (x : Ainf p R) :
    g • algebraMap _ (BdRPlus p R) x = algebraMap _ _ (g • x) := BdRPlus.map_algebraMap_ainf _ x
theorem BdR.smul_algebraMap (g : G) (x : BdRPlus p R) :
    g • algebraMap _ (BdR p R) x = algebraMap _ _ (g • x) := BdR.map_algebraMap _ x
theorem Acris.smul_algebraMap (g : G) (x : Ainf p R) :
    g • algebraMap _ (Acris p R) x = algebraMap _ _ (g • x) := Acris.map_algebraMap _ x
theorem BcrisPlus.smul_algebraMap (g : G) (x : Acris p R) :
    g • algebraMap _ (BcrisPlus p R) x = algebraMap _ _ (g • x) := BcrisPlus.map_algebraMap _ x
theorem Bcris.smul_algebraMap (g : G) (x : BcrisPlus p R) :
    g • algebraMap _ (Bcris p R) x = algebraMap _ _ (g • x) := Bcris.map_algebraMap _ _ x
theorem Bcris.smul_algebraMap_acris (g : G) (x : Acris p R) :
    g • algebraMap _ (Bcris p R) x = algebraMap _ _ (g • x) := Bcris.map_algebraMap_acris _ _ x
theorem Bst.smul_algebraMap (g : G) (x : Bcris p R) :
    g • algebraMap _ (Bst p R) x = algebraMap _ _ (g • x) := Bst.map_algebraMap _ _ x

theorem smulCommClass_of_fixed {K B : Type*} [CommRing K] [CommRing B] [Algebra K B]
    [MulSemiringAction G B] (h : ∀ (g : G) (a : K), g • algebraMap K B a = algebraMap K B a) :
    SMulCommClass G K B :=
  ⟨fun g a x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', h]⟩

omit [IsAdicComplete (span {(p : R)}) R] in
instance : SMulCommClass G ℤ_[p] (Ainf p R) :=
  smulCommClass_of_fixed fun _ a => Ainf.map_algebraMap _ a
instance : SMulCommClass G ℤ_[p] (Acris p R) :=
  smulCommClass_of_fixed fun _ a => Acris.map_algebraMap_padicInt _ a
instance : SMulCommClass G ℚ_[p] (BdRPlus p R) :=
  smulCommClass_of_fixed fun _ a => BdRPlus.map_algebraMap_padic _ a
instance : SMulCommClass G ℚ_[p] (BdR p R) :=
  smulCommClass_of_fixed fun _ a => BdR.map_algebraMap_padic _ a
instance : SMulCommClass G ℚ_[p] (BcrisPlus p R) :=
  smulCommClass_of_fixed fun _ a => BcrisPlus.map_algebraMap_padic _ a
instance : SMulCommClass G ℚ_[p] (Bcris p R) :=
  smulCommClass_of_fixed fun _ a => Bcris.map_algebraMap_padic _ _ a
instance : SMulCommClass G ℚ_[p] (Bst p R) :=
  smulCommClass_of_fixed fun _ a => Bst.map_algebraMap_padic _ _ a

omit [IsAdicComplete (span {(p : R)}) R] in
theorem Ainf.smul_frob (g : G) (x : Ainf p R) : g • Ainf.frob p R x = Ainf.frob p R (g • x) :=
  Ainf.map_frob _ x
theorem Acris.smul_frob (g : G) (x : Acris p R) : g • Acris.frob p R x = Acris.frob p R (g • x) :=
  Acris.map_frob _ x
theorem BcrisPlus.smul_frob (g : G) (x : BcrisPlus p R) :
    g • BcrisPlus.frob p R x = BcrisPlus.frob p R (g • x) := BcrisPlus.map_frob _ x
theorem Bcris.smul_frob (g : G) (x : Bcris p R) : g • Bcris.frob p R x = Bcris.frob p R (g • x) :=
  Bcris.map_frob _ _ x
theorem Bst.smul_frob (g : G) (x : Bst p R) : g • Bst.frob p R x = Bst.frob p R (g • x) :=
  Bst.map_frob _ _ x
theorem Bst.monodromy_smul (g : G) (x : Bst p R) :
    Bst.monodromy p R (g • x) = g • Bst.monodromy p R x := Bst.monodromy_map _ _ x

theorem BdRPlus.smul_mem_fil (g : G) {n : ℕ} {x : BdRPlus p R} (hx : x ∈ BdRPlus.fil p R n) :
    g • x ∈ BdRPlus.fil p R n := BdRPlus.map_mem_fil _ hx
theorem BdR.smul_mem_fil (g : G) {i : ℤ} {x : BdR p R} (hx : x ∈ BdR.fil p R i) :
    g • x ∈ BdR.fil p R i := BdR.map_mem_fil _ hx

theorem Acris.smul_logTeich (g : G) (η : tateModule p R) :
    g • Acris.logTeich η = Acris.logTeich (g • η) := Acris.map_logTeich _ η
theorem Bcris.smul_logTeich (g : G) (η : tateModule p R) :
    g • Bcris.logTeich η = Bcris.logTeich (g • η) := Bcris.map_logTeich _ _ η
theorem Bst.smul_logFlat (g : G) (ϖ : PFlat p R) :
    g • Bst.logFlat ϖ = Bst.logFlat (g • ϖ) := Bst.map_logFlat _ _ ϖ

end Reformulated.AutPerF
