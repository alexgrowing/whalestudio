import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F] {n M N : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  rw [GroundTheory.Global.mem_integralFiniteAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem mem_KLev {g : GL (Fin n) (Af F)} :
    g ∈ KLev F n M ↔ (∀ a b, g a b ∈ Ohat F) ∧ (∀ a b, (g⁻¹ : GL (Fin n) (Af F)) a b ∈ Ohat F) ∧
      ∀ a b, ∃ y ∈ Ohat F, g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b = (M : Af F) * y := by
  have h1 : ∀ a b, (((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b : ↥(Ohat F)) : Af F) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  have h2 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))})) a b =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b) := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun a b => (k a b).2, fun a b => ?_, fun a b => ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin n) ↥(Ohat F)) a b).2
    · have e : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}) (k a b) = _ :=
        (congrArg (fun x : GL (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))}) => x a b) hk).trans (h2 a b)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e)
      refine ⟨y, y.2, ?_⟩
      rw [← h1]
      exact congrArg Subtype.val hy
  · rintro ⟨ha, hb, hc⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ohat F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin n) ↥(Ohat F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin n) (Af F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, ?_, Units.ext rfl⟩
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine Eq.trans ?_ (h2 a b).symm
    obtain ⟨y, hy, e⟩ := hc a b
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    rw [← h1] at e
    exact e

theorem KLev_le_of_dvd (h : M ∣ N) : KLev F n N ≤ KLev F n M := by
  obtain ⟨c, rfl⟩ := h
  intro g hg
  obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
  refine mem_KLev.2 ⟨ha, hb, fun a b => ?_⟩
  obtain ⟨y, hy, e⟩ := hc a b
  exact ⟨c * y, mul_mem (natCast_mem _ c) hy, by rw [e, Nat.cast_mul, mul_assoc]⟩

theorem KLev_le_integral : KLev F n M ≤ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F n := fun _ hg =>
  (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff F n).2
    ⟨fun a b => mem_Ohat.1 ((mem_KLev.1 hg).1 a b), fun a b => mem_Ohat.1 ((mem_KLev.1 hg).2.1 a b)⟩

theorem isOpen_Ohat : IsOpen (Ohat F : Set (Af F)) := by
  convert GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F) using 1
  exact Set.ext fun _ => mem_Ohat

theorem isOpen_KLev (hM : 1 ≤ M) : IsOpen (KLev F n M : Set (GL (Fin n) (Af F))) := by
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set u : Af F := algebraMap F (Af F) (M : F)⁻¹
  have hu : u * M = 1 := by rw [← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have e : (KLev F n M : Set (GL (Fin n) (Af F))) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => g a b) ⁻¹' Ohat F) ∩
      ((⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => (g⁻¹ : GL (Fin n) (Af F)) a b) ⁻¹' Ohat F) ∩
      ⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => u * (g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b)) ⁻¹' Ohat F) := by
    ext g
    simp only [SetLike.mem_coe, mem_KLev, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun a b => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
    · rintro ⟨y, hy, e⟩
      rwa [e, ← mul_assoc, hu, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]
  rw [e]
  have c : ∀ a b, Continuous fun g : GL (Fin n) (Af F) => g a b := fun a b =>
    Continuous.matrix_elem Units.continuous_val a b
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_) <;>
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_Ohat.preimage ?_
  · exact c a b
  · exact (c a b).comp continuous_inv
  · exact continuous_const.mul ((c a b).sub continuous_const)

theorem isCompact_KLev (hM : 1 ≤ M) : IsCompact (KLev F n M : Set (GL (Fin n) (Af F))) :=
  (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev hM)) KLev_le_integral

theorem HasFixed.mono {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V} {U U' : Subgroup Γ}
    (h : HasFixed ρ U) (hU : U' ≤ U) : HasFixed ρ U' :=
  let ⟨v, h0, hv⟩ := h
  ⟨v, h0, fun u hu => hv u (hU hu)⟩

end UpperTheory.V.Af
