import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC

theorem span_top_of_image {L : Type*} [Field L] (e : L →+* ℂ) {M V : Type*} [AddCommGroup M] [Module L M] [AddCommGroup V]
    [Module ℂ V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M) (hb1 : LinearIndependent ℂ (fun k => jm (b k)))
    (hb2 : Submodule.span ℂ (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span ℂ (jm '' S) = ⊤) :
    Submodule.span L S = ⊤ := by
  by_contra hW
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top (Submodule.span L S) (lt_top_iff_ne_top.2 hW)
  let bC : Module.Basis ι ℂ V := Module.Basis.mk hb1 (le_of_eq hb2.symm)
  let F : V →ₗ[ℂ] ℂ := bC.constr ℂ fun k => e (f (b k))
  have hFb : ∀ k, F (jm (b k)) = e (f (b k)) := fun k => by
    have h : jm (b k) = bC k := (Module.Basis.mk_apply hb1 (le_of_eq hb2.symm) k).symm
    rw [h, Module.Basis.constr_basis]
  have hFj : ∀ x, F (jm x) = e (f x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hFb k
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hF0 : F = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Submodule.span ℂ (jm '' S) := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hFj, show f x = 0 from hfW (Submodule.subset_span hx), map_zero]; rfl
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  apply hf0
  refine LinearMap.ext fun x => e.injective ?_
  rw [← hFj, hF0]
  simp

section Loc

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {P : Type*} [AddCommGroup P] [Module K P] [Module O P] [IsScalarTower O K P]

theorem isLocalized_of_span (N : Submodule O P) (hN : Submodule.span K (N : Set P) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) N.subtype := by
  have hK : ∀ s ∈ nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s hs =>
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero hs)
  refine ⟨fun s => ?_, fun y => ?_, fun {a b} h => ⟨1, by simpa using Subtype.ext h⟩⟩
  · rw [Module.End.isUnit_iff]
    have hs := hK s s.2
    refine ⟨fun x y hxy => ?_, fun y => ⟨(algebraMap O K s)⁻¹ • y, ?_⟩⟩
    · have h1 : (algebraMap O K s) • x = (algebraMap O K s) • y := by
        simpa [algebraMap_smul] using hxy
      exact (smul_right_injective P hs) h1
    · show (s : O) • ((algebraMap O K s)⁻¹ • y) = y
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · have hy : y ∈ Submodule.span K (N : Set P) := hN ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨⟨⟨x, hx⟩, 1⟩, by simp⟩
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨⟨b, t⟩, hb⟩ := hy
      refine ⟨⟨(t : O) • a + (s : O) • b, s * t⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul] at ha hb ⊢
      rw [← ha, ← hb, Submonoid.coe_mul, smul_add, mul_smul, mul_smul, smul_comm (t : O) (s : O) x]
    | smul c x _ hx =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
      refine ⟨⟨n • a, ⟨d, hd⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_smul] at ha ⊢
      rw [← ha, Submonoid.coe_mul, mul_smul]
      change (d : O) • (s : O) • ((algebraMap O K n / algebraMap O K d) • x) = n • (s : O) • x
      rw [← algebraMap_smul K (d : O), ← algebraMap_smul K (s : O), ← algebraMap_smul K n, ← algebraMap_smul K (s : O) x,
        smul_smul, smul_smul, smul_smul]
      congr 1
      have hd0 : algebraMap O K d ≠ 0 := hK d hd
      field_simp

end Loc

theorem span_image_top {L : Type*} [Field L] {K : Type*} [Field K] (e : L →+* K) {M V : Type*} [AddCommGroup M] [Module L M]
    [AddCommGroup V] [Module K V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M)
    (hb2 : Submodule.span K (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span L S = ⊤) :
    Submodule.span K (jm '' S) = ⊤ := by
  refine le_antisymm le_top (hb2 ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have key : ∀ x ∈ Submodule.span L S, jm x ∈ Submodule.span K (jm '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  exact key _ (hS ▸ Submodule.mem_top)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂}

theorem span_latL (i : LocT B) : Submodule.span what₂.LL (latL B i) = ⊤ := by
  have hb := what₂.jMt_basis (what₂.muTw (wOf B i)) (jOf B i) (Module.Free.chooseBasis what₂.LL _)
  refine span_top_of_image what₂.embLL (what₂.jMt (what₂.muTw (wOf B i)) (jOf B i)) _ hb.1 hb.2 _ ?_
  have h := (what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).span_top
  refine le_antisymm le_top (h ▸ Submodule.span_mono fun v hv => ?_)
  obtain ⟨x, rfl⟩ := what₂.MtLat_sub _ _ v hv
  exact ⟨x, hv, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem span_mtSub (hC : PartCompl B) (i : LocT B) :
    Submodule.span (FractionRing (OOf B i)) ((MtSub B hC i : Submodule (OOf B i) (partOf B i)) : Set (partOf B i)) = ⊤ := by
  have hV := span_image_top (B.ec (jOf B i) (wOf B i)) (B.iV (jOf B i) (wOf B i)) (Module.Free.chooseBasis what₂.LL _)
    (B.iV_basis (jOf B i) (wOf B i) _).2 _ (span_latL i)
  refine le_antisymm le_top ?_
  rintro y -
  obtain ⟨x, rfl⟩ := Submodule.projectionOnto_surjective (hC i) y
  have hx : x ∈ Submodule.span (FractionRing (OOf B i)) (B.iV (jOf B i) (wOf B i) '' latL B i) := hV ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, rfl⟩ := hz
    exact Submodule.subset_span (Submodule.subset_span ⟨u, hu, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

set_option synthInstance.maxHeartbeats 400000 in

theorem mtLoc_holds (hC : PartCompl B) : MtLoc B hC := fun i => isLocalized_of_span _ (span_mtSub hC i)

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
