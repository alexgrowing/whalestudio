import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.InnerDual

theorem unif_mem_maximal {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : Ideal L.O) (hm : m.IsMaximal) :
    (⟨algebraMap F E ϖ, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2⟩ : L.O) ∈ m := by
  classical

  let φ : 𝒪[F] →+* L.O := ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O
    (fun c => (GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  have hcomp : (L.O.subtype).comp φ = algebraMap 𝒪[F] E := by
    ext c
    rfl
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨p, hp, hpx⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    have key := Polynomial.hom_eval₂ p φ L.O.subtype x
    rw [hcomp] at key
    show L.O.subtype (Polynomial.eval₂ φ x p) = L.O.subtype 0
    rw [key, map_zero]
    exact hpx

  have := hm
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint m
  have h3 : ϖ ∈ m.comap φ := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  exact Ideal.mem_comap.1 h3

end GlobalTheory.LocOver.InnerDual

namespace GlobalTheory.LocOver.InnerDual

open GlobalTheory.LocOver.UnipOnto in

theorem exists_inner_lattice_vector_anisotropic' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)),
    H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr L hL
  have : IsNonarchimedeanLocalField F := hM.loc
  have : CharZero F := hM.char0
  classical
  obtain ⟨_hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : (xz : V) = Fr.f (Fin.last r) := hxz

  have hint : ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L →
      H.h (Fr.f (Fin.last r)) (y : V) ∈ M.L.O := by
    intro y hy
    have h0 := (hdual xz).1 hxzL y hy
    rwa [hz] at h0

  obtain ⟨I, hI⟩ : ∃ I : Ideal M.L.O, ∀ c : M.L.O, c ∈ I ↔
      ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = (c : E) :=
    ⟨{ carrier := {c | ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧
          H.h (Fr.f (Fin.last r)) (y : V) = (c : E)}
       add_mem' := by
         rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hyb⟩
         refine ⟨y + y', by rw [map_add]; exact L.add_mem hy hy', ?_⟩
         show H.h _ ((y : V) + (y' : V)) = (a : E) + (b : E)
         rw [h_add_right, hya, hyb]
       zero_mem' := by
         refine ⟨0, by rw [map_zero]; exact L.zero_mem, ?_⟩
         show H.h _ (0 : V) = 0
         exact h_zero_right H _
       smul_mem' := by
         rintro c a ⟨y, hy, hya⟩
         refine ⟨M.L.cj (c : E) • y, ?_, ?_⟩
         · rw [map_smul]
           exact L.smul_mem ⟨M.L.cj (c : E), GlobalTheory.UnramOrder.cj_mem M.L c.2⟩ hy
         · show H.h _ (M.L.cj (c : E) • (y : V)) = (c : E) * (a : E)
           rw [h_smul_right, M.L.cj_cj, hya] },
     fun c => Iff.rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have : IsPrincipalIdealRing M.L.O := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal m
    have hϖm := unif_mem_maximal M.L ϖ hϖ m hm
    rw [hπ, Submodule.mem_span_singleton] at hϖm
    obtain ⟨t, ht⟩ := hϖm
    have htE : (t : E) * (π : E) = algebraMap F E ϖ := congrArg Subtype.val ht
    obtain ⟨πi, hπi⟩ : ∃ πi : E, πi = (t : E) * algebraMap F E (ϖ : F)⁻¹ := ⟨_, rfl⟩
    have hinv : πi * (π : E) = 1 := by
      rw [hπi, mul_right_comm, htE, ← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    have hvL : H.mkW Fr.f (πi • xz) ∈ L := by
      refine (hdual (πi • xz)).2 fun y hy => ?_
      have hyI : (⟨_, hint y hy⟩ : M.L.O) ∈ I := (hI _).2 ⟨y, hy, rfl⟩
      have hym := hIm hyI
      rw [hπ, Submodule.mem_span_singleton] at hym
      obtain ⟨s, hs⟩ := hym
      have hsE : (s : E) * (π : E) = H.h (Fr.f (Fin.last r)) (y : V) := congrArg Subtype.val hs
      show H.h (πi • (xz : V)) (y : V) ∈ M.L.O
      rw [H.h_smul_left, hz, ← hsE, mul_left_comm, hinv, mul_one]
      exact s.2
    have hxzv : H.mkW Fr.f xz = (π : E) • H.mkW Fr.f (πi • xz) := by
      refine Eq.trans ?_ (map_smul (H.mkW Fr.f) (π : E) (πi • xz))
      congr 1
      apply Subtype.ext
      show (xz : V) = (π : E) • (πi • (xz : V))
      rw [smul_smul, mul_comm, hinv, one_smul]
    have hu := hprim π (πi • xz) hvL hxzv
    exact hm.ne_top (hπ.trans (Ideal.span_singleton_eq_top.2 hu))
  have h1 : (1 : M.L.O) ∈ I := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y0, hy0L, hy0z⟩ := (hI 1).1 h1
  have hy0z' : H.h (Fr.f (Fin.last r)) (y0 : V) = 1 := hy0z

  obtain ⟨w, hw⟩ : ∃ w : V, w = ∑ a : Fin r, H.h (y0 : V) (Fr.es a) • Fr.f a.castSucc := ⟨_, rfl⟩
  have hwX : w ∈ H.X Fr.f := by
    rw [hw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Fj_le_X Fr _ (e_mem Fr a))
  have hwp : w ∈ H.perp (H.X Fr.f) := X_le_perp Fr hwX
  have hsumL : ∀ (g : Fin r → V) (u : V) (s : Finset (Fin r)),
      H.h (∑ a ∈ s, g a) u = ∑ a ∈ s, H.h (g a) u := by
    intro g u s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.sum_empty]
      exact H.h_zero_left u
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  refine ⟨y0 - ⟨w, hwp⟩, ?_, ?_, ?_⟩
  · have hmk0 : H.mkW Fr.f ⟨w, hwp⟩ = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hwX
    rw [map_sub, hmk0, sub_zero]
    exact hy0L
  · show H.h _ ((y0 : V) - w) = 1
    rw [h_sub_right, h_right H _ w, pairing_isotropicSpan_lastVector Fr w hwX, map_zero, sub_zero, hy0z']
  · intro b
    show H.h ((y0 : V) - w) (Fr.es b) = 0
    rw [h_sub_left, hw, hsumL]
    simp [H.h_smul_left, Fr.h_es]

end GlobalTheory.LocOver.InnerDual
