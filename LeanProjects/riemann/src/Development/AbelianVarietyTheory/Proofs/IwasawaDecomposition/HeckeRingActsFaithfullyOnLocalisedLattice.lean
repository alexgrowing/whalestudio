import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocAct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂}

theorem apply_eq_smul (hss : SemisimpleTw B) (i : LocT B) (ψ : hAlg B i →ₐ[OOf B i] OOf B i)
    {x : B.V (jOf B i) (wOf B i)} (hx : x ∈ NCov.W (hAlg B i) (NCov.pt ψ)) (t : hAlg B i) :
    (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) x =
      algebraMap (OOf B i) (FractionRing (OOf B i)) (ψ t) • x := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem e he =>
    obtain ⟨v, k, hvk, rfl⟩ := he
    have h1 := NCov.W_le _ _ (⟨_, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ : hAlg B i) hx
    have hs := hss (jOf B i) (wOf B i) i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 v k hvk
    rw [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    exact Module.End.mem_eigenspace_iff.1 h1
  | algebraMap r =>
    have e : ψ ⟨algebraMap (OOf B i) _ r, Subalgebra.algebraMap_mem _ r⟩ = r := ψ.commutes r
    rw [e]
    show (algebraMap (OOf B i) (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) r) x = _
    rw [Module.algebraMap_end_apply, algebraMap_smul]
  | add a b ha hb iha ihb =>
    have e : ψ ⟨a + b, add_mem ha hb⟩ = ψ ⟨a, ha⟩ + ψ ⟨b, hb⟩ := map_add ψ ⟨a, ha⟩ ⟨b, hb⟩
    change a x = _ at iha
    change b x = _ at ihb
    show (a + b) x = _
    rw [e, LinearMap.add_apply, iha, ihb, map_add, add_smul]
  | mul a b ha hb iha ihb =>
    have e : ψ ⟨a * b, mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ := map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩
    change a x = _ at iha
    change b x = _ at ihb
    show (a * b) x = _
    rw [e, Module.End.mul_apply, ihb, map_smul, iha, smul_smul, map_mul, mul_comm]

section Gen
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_iSup₂_of_mapsTo {ι : Type*} (p : ι → Submodule K V) (P : ι → Prop) (f : Module.End K V)
    (h : ∀ a, P a → ∀ x ∈ p a, f x ∈ p a) {y : V} (hy : y ∈ ⨆ (a) (_ : P a), p a) : f y ∈ ⨆ (a) (_ : P a), p a := by
  have hle : (⨆ (a) (_ : P a), p a) ≤ (⨆ (a) (_ : P a), p a).comap f :=
    iSup₂_le fun a ha x hx => le_iSup₂ (f := fun a (_ : P a) => p a) a ha (h a ha x hx)
  exact hle hy

theorem eq_zero_of_iSup₂ {ι : Type*} (p : ι → Submodule K V) (P : ι → Prop) (f : Module.End K V)
    (h : ∀ a, P a → ∀ x ∈ p a, f x = 0) {y : V} (hy : y ∈ ⨆ (a) (_ : P a), p a) : f y = 0 := by
  have hle : (⨆ (a) (_ : P a), p a) ≤ LinearMap.ker f := iSup₂_le fun a ha x hx => h a ha x hx
  exact hle hy

end Gen

theorem mem_part (hss : SemisimpleTw B) (i : LocT B) (t : hAlg B i) {y : B.V (jOf B i) (wOf B i)}
    (hy : y ∈ partOf B i) : (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y ∈ partOf B i :=
  mem_iSup₂_of_mapsTo (fun ψ : hAlg B i →ₐ[OOf B i] OOf B i => NCov.W (hAlg B i) (NCov.pt ψ)) (fun ψ => NCov.cls ψ = i.2.1) _
    (fun ψ _ z hz => by
      rw [apply_eq_smul hss i ψ hz t]
      exact Submodule.smul_mem _ _ hz) hy

theorem mem_off (hss : SemisimpleTw B) (i : LocT B) (t : hAlg B i) {y : B.V (jOf B i) (wOf B i)}
    (hy : y ∈ offOf B i) : (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y ∈ offOf B i :=
  mem_iSup₂_of_mapsTo (fun ψ : hAlg B i →ₐ[OOf B i] OOf B i => NCov.W (hAlg B i) (NCov.pt ψ)) (fun ψ => NCov.cls ψ ≠ i.2.1) _
    (fun ψ _ z hz => by
      rw [apply_eq_smul hss i ψ hz t]
      exact Submodule.smul_mem _ _ hz) hy

theorem eq_zero_of_pts (hss : SemisimpleTw B) (i : LocT B) (t : hAlg B i) (ht : ∀ x : XOf B i, x.1 t = 0)
    {y : B.V (jOf B i) (wOf B i)} (hy : y ∈ partOf B i) :
    (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y = 0 :=
  eq_zero_of_iSup₂ (fun ψ : hAlg B i →ₐ[OOf B i] OOf B i => NCov.W (hAlg B i) (NCov.pt ψ)) (fun ψ => NCov.cls ψ = i.2.1) _
    (fun ψ hψ z hz => by
      rw [apply_eq_smul hss i ψ hz t]
      by_cases hW : NCov.W (hAlg B i) (NCov.pt ψ) = ⊥
      · rw [hW] at hz
        rw [(Submodule.mem_bot _).1 hz, smul_zero]
      · rw [ht ⟨ψ, hψ, hW⟩, map_zero, zero_smul]) hy

theorem projOf_apply (hss : SemisimpleTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i) (y : B.V (jOf B i) (wOf B i)) :
    ((projOf B hC i ((t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y) : partOf B i) :
      B.V (jOf B i) (wOf B i)) = (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) (projOf B hC i y) := by
  have hq : y - ((projOf B hC i y : partOf B i) : B.V (jOf B i) (wOf B i)) ∈ offOf B i :=
    Submodule.sub_projection_mem (hC i) y
  have e : (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y =
      (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) (projOf B hC i y) +
      (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) (y - (projOf B hC i y : B.V (jOf B i) (wOf B i))) := by
    rw [← map_add, add_sub_cancel]
  have h1 : projOf B hC i ((t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) (projOf B hC i y)) =
      ⟨_, mem_part hss i t (projOf B hC i y).2⟩ :=
    Submodule.projectionOnto_apply_of_mem_left (hC i) _
  have h2 : projOf B hC i ((t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)))
      (y - (projOf B hC i y : B.V (jOf B i) (wOf B i)))) = 0 :=
    Submodule.projectionOnto_apply_of_mem_right (hC i) (mem_off hss i t hq)
  rw [e, map_add, h1, h2, add_zero]

def lat0 (i : LocT B) : Submodule (OOf B i) (B.V (jOf B i) (wOf B i)) :=
  Submodule.span (OOf B i) (B.iV (jOf B i) (wOf B i) '' latL B i)

theorem heckeGenerator_mapsTo_localisationLatticeSpan (hI : HeckeIntTw B) (i : LocT B) {v : HeightOneSpectrum (𝓞 H.E)} {k : ℕ}
    (hvk : GenAt0 H (what₂.places.resChar (wOf B i)) (B.Qw (wOf B i)) v k) {z : B.V (jOf B i) (wOf B i)}
    (hz : z ∈ lat0 i) : B.hK (jOf B i) (wOf B i) v k z ∈ lat0 i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨F, c, hF, hc, he⟩ := hI (jOf B i) (wOf B i) i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 v k hvk x hx
    rw [B.hK_def, he, map_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [LinearMap.map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w (jOf B i) (wOf B i) (c y)).1 (hc y hy)
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hF hy, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul o a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ ha

theorem heckeAlgebra_mapsTo_localisationLatticeSpan (hI : HeckeIntTw B) (i : LocT B) (t : hAlg B i) {z : B.V (jOf B i) (wOf B i)}
    (hz : z ∈ lat0 i) : (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) z ∈ lat0 i := by
  obtain ⟨t, ht⟩ := t
  show t z ∈ lat0 i
  induction ht using Algebra.adjoin_induction generalizing z with
  | mem e he =>
    obtain ⟨v, k, hvk, rfl⟩ := he
    exact heckeGenerator_mapsTo_localisationLatticeSpan hI i hvk hz
  | algebraMap r =>
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_of_tower_mem _ r hz
  | add a b _ _ ha hb => rw [LinearMap.add_apply]; exact Submodule.add_mem _ (ha hz) (hb hz)
  | mul a b _ _ ha hb => rw [Module.End.mul_apply]; exact ha (hb hz)

theorem projOf_mem (hC : PartCompl B) (i : LocT B) {z : B.V (jOf B i) (wOf B i)} (hz : z ∈ lat0 i) :
    projOf B hC i z ∈ MtSub B hC i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul o a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ ha

theorem mem_MtSub (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i)
    {m : partOf B i} (hm : m ∈ MtSub B hC i) :
    (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) m, mem_part hss i t m.2⟩ : partOf B i) ∈
      MtSub B hC i := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    have e : (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)))
        (projOf B hC i (B.iV (jOf B i) (wOf B i) x)), mem_part hss i t (projOf B hC i _).2⟩ : partOf B i) =
        projOf B hC i ((t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) (B.iV (jOf B i) (wOf B i) x)) :=
      Subtype.ext (projOf_apply hss hC i t _).symm
    rw [e]
    exact projOf_mem hC i (heckeAlgebra_mapsTo_localisationLatticeSpan hI i t (Submodule.subset_span ⟨x, hx, rfl⟩))
  | zero =>
    have e : (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((0 : partOf B i) : B.V (jOf B i) (wOf B i)),
        mem_part hss i t (0 : partOf B i).2⟩ : partOf B i) = 0 := Subtype.ext (by simp)
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((a + b : partOf B i) : B.V (jOf B i) (wOf B i)),
        mem_part hss i t (a + b).2⟩ : partOf B i) =
        ⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) a, mem_part hss i t a.2⟩ +
        ⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) b, mem_part hss i t b.2⟩ :=
      Subtype.ext (by simp)
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul o a _ ha =>
    have e : (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((o • a : partOf B i) : B.V (jOf B i) (wOf B i)),
        mem_part hss i t (o • a).2⟩ : partOf B i) =
        o • (⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) a, mem_part hss i t a.2⟩ : partOf B i) :=
      Subtype.ext (by simp [Submodule.coe_smul_of_tower, LinearMap.map_smul_of_tower])
    rw [e]; exact Submodule.smul_mem _ _ ha

def resL (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i) :
    Module.End (OOf B i) (MtSub B hC i) where
  toFun m := ⟨⟨(t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((m : partOf B i) : B.V (jOf B i) (wOf B i)),
    mem_part hss i t (m : partOf B i).2⟩, mem_MtSub hss hI hC i t m.2⟩
  map_add' a b := by
    apply Subtype.ext; apply Subtype.ext
    simp
  map_smul' o a := by
    apply Subtype.ext; apply Subtype.ext
    simp [Submodule.coe_smul_of_tower, LinearMap.map_smul_of_tower]

theorem resL_apply (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i)
    (m : MtSub B hC i) : (((resL hss hI hC i t m : MtSub B hC i) : partOf B i) : B.V (jOf B i) (wOf B i)) =
      (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((m : partOf B i) : B.V (jOf B i) (wOf B i)) := rfl

def resA (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) :
    hAlg B i →ₐ[OOf B i] Module.End (OOf B i) (MtSub B hC i) where
  toFun := resL hss hI hC i
  map_one' := by ext m; rfl
  map_mul' a b := by ext m; rfl
  map_zero' := by ext m; rfl
  map_add' a b := by ext m; rfl
  commutes' r := by
    ext m
    show (algebraMap (OOf B i) (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) r)
      ((m : partOf B i) : B.V (jOf B i) (wOf B i)) = _
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    simp [Submodule.coe_smul_of_tower]

def evA (i : LocT B) : hAlg B i →ₐ[OOf B i] (XOf B i → OOf B i) where
  toFun t x := x.1 t
  map_one' := by funext x; exact map_one x.1
  map_mul' a b := by funext x; exact map_mul x.1 a b
  map_zero' := by funext x; exact map_zero x.1
  map_add' a b := by funext x; exact map_add x.1 a b
  commutes' r := by funext x; exact x.1.commutes r

theorem evA_gen (i : LocT B) {v : HeightOneSpectrum (𝓞 H.E)} {k : ℕ}
    (hvk : GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k) :
    evA i ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = hTfun B i v k := by
  funext x
  simp [evA, hTfun, dif_pos hvk]

theorem evA_mem (i : LocT B) (t : hAlg B i) : evA i t ∈ TOf B i := by
  have hle : (Algebra.adjoin (OOf B i) (((↑) : hAlg B i → Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ⁻¹'
      {f | ∃ v k, GenAt0 H (what₂.places.resChar (wOf B i)) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k})).map (evA i) ≤
      TOf B i := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, k, hvk, he⟩ := hz
    have e : z = ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := Subtype.ext he
    rw [e, evA_gen i hvk]
    exact Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩
  apply hle
  refine Subalgebra.mem_map.2 ⟨t, ?_, rfl⟩
  rw [Algebra.adjoin_adjoin_coe_preimage]
  exact Algebra.mem_top

def evT (i : LocT B) : hAlg B i →ₐ[OOf B i] TOf B i := (evA i).codRestrict (TOf B i) (evA_mem i)

theorem evT_surjective (i : LocT B) : Function.Surjective (evT i) := by
  intro f
  have hle : TOf B i ≤ (evA i).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨_, evA_gen i hvk⟩
  obtain ⟨t, ht⟩ := hle f.2
  exact ⟨t, Subtype.ext ht⟩

def actR (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) :
    TOf B i →+* Module.End (OOf B i) (MtSub B hC i) :=
  RingHom.liftOfSurjective (evT i).toRingHom (evT_surjective i)
    ⟨(resA hss hI hC i).toRingHom, fun t ht => by
      rw [RingHom.mem_ker] at ht ⊢
      have h0 : ∀ x : XOf B i, x.1 t = 0 := fun x => congrFun (congrArg Subtype.val ht) x
      ext m
      exact eq_zero_of_pts hss i t h0 (m : partOf B i).2⟩

theorem actR_evT (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i) :
    actR hss hI hC i (evT i t) = resA hss hI hC i t :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ t

def actA (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) :
    TOf B i →ₐ[OOf B i] Module.End (OOf B i) (MtSub B hC i) where
  toRingHom := actR hss hI hC i
  commutes' r := by
    have e : algebraMap (OOf B i) (TOf B i) r = evT i (algebraMap (OOf B i) (hAlg B i) r) := ((evT i).commutes r).symm
    show actR hss hI hC i (algebraMap (OOf B i) (TOf B i) r) = _
    rw [e, actR_evT, AlgHom.commutes]

theorem actA_evT (hss : SemisimpleTw B) (hI : HeckeIntTw B) (hC : PartCompl B) (i : LocT B) (t : hAlg B i) :
    actA hss hI hC i (evT i t) = resA hss hI hC i t :=
  actR_evT hss hI hC i t

theorem actEx_of : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B),
    MtLoc B (partCompl_of hs hd) → HeckeIntTw B → SemisimpleTw B → ActEx B (partCompl_of hs hd) := by
  intro R H what₂ B hs hd hL hI hss i
  refine ⟨actA hss hI (partCompl_of hs hd) i, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨t, rfl⟩ := evT_surjective i f
    rw [actA_evT] at hf
    have hkill : ∀ y ∈ partOf B i, (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) y = 0 := by
      intro y hy
      haveI := hL i
      obtain ⟨⟨m, s⟩, hsm⟩ := IsLocalizedModule.surj (nonZeroDivisors (OOf B i)) (MtSub B (partCompl_of hs hd) i).subtype
        (⟨y, hy⟩ : partOf B i)
      have hsm' : (s : OOf B i) • y = ((m : partOf B i) : B.V (jOf B i) (wOf B i)) := congrArg Subtype.val hsm
      have hm0 : (t : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) ((m : partOf B i) : B.V (jOf B i) (wOf B i)) = 0 := by
        rw [← resL_apply hss hI (partCompl_of hs hd) i t m]
        show (((resA hss hI (partCompl_of hs hd) i t m : MtSub B (partCompl_of hs hd) i) : partOf B i) : B.V (jOf B i) (wOf B i)) = 0
        rw [hf]; rfl
      rw [← hsm', LinearMap.map_smul_of_tower, ← algebraMap_smul (FractionRing (OOf B i))] at hm0
      exact (smul_eq_zero.1 hm0).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2)
    apply Subtype.ext
    funext x
    show x.1 t = 0
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.2
    have hzp : z ∈ partOf B i :=
      le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ)) x.1 x.2.1 hz
    have h1 := hkill z hzp
    rw [apply_eq_smul hss i x.1 hz t] at h1
    exact (IsFractionRing.to_map_eq_zero_iff (K := FractionRing (OOf B i))).1 ((smul_eq_zero.1 h1).resolve_right hz0)
  · intro v k hvk m
    have e : hTOf B i v k = evT i ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
      apply Subtype.ext
      rw [show ((evT i ⟨B.hK (jOf B i) (wOf B i) v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ : TOf B i) : XOf B i → OOf B i) =
        hTfun B i v k from evA_gen i hvk]
      simp [hTOf, dif_pos hvk]
    rw [e, actA_evT]
    rfl

end GlobalTheory.HeckeLocAct
