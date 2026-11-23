import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSZpowIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardKilledByInType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoRawMulIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvMulIntAway
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Formalism.LocalToGlobal.Columns.InputsGenus
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.InertNbr

section Labels

theorem labIn_eq (n : ℕ) (s : List ℕ) : labIn n s = s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++
    s.reverse.map (fun a : ℕ => -(a : ℤ)) := by
  have e : ∀ l : List ℕ, (l.flatMap fun a : ℕ => [(a : ℤ)]) = l.map fun a : ℕ => (a : ℤ) := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.flatMap_cons, ih]; rfl
  show (s.flatMap fun a : ℕ => [(a : ℤ)]).map (fun a => a) ++ _ ++
    (s.reverse.flatMap fun a : ℕ => [(a : ℤ)]).map (fun a => -a) = _
  rw [e, e, List.map_map, List.map_map]
  rfl

theorem labIn_length {n : ℕ} {s : List ℕ} (h : 2 * s.length ≤ n) : (labIn n s).length = n := by
  simp only [labIn_eq, List.length_append, List.length_map, List.length_replicate, List.length_reverse]
  omega

theorem dualLab_labIn (n : ℕ) (s : List ℕ) : dualLab (labIn n s) = labIn n s := by
  simp [dualLab, labIn_eq, List.map_reverse, Function.comp_def]

theorem labIn_pairwise (n : ℕ) {s : List ℕ} (h : s.Pairwise (· ≥ ·)) : (labIn n s).Pairwise fun a b => b ≤ a := by
  rw [labIn_eq]
  rw [List.pairwise_append, List.pairwise_append, List.pairwise_map, List.pairwise_map, List.pairwise_reverse]
  refine ⟨⟨h.imp fun h => by omega, by simp, ?_⟩, h.imp fun h => by omega, ?_⟩
  · intro a ha b hb
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]; omega
  · intro a ha b hb
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]; omega

theorem posPart_labIn (n : ℕ) {s : List ℕ} (h : ∀ a ∈ s, 0 < a) : posPart (labIn n s) = s := by
  rw [labIn_eq]
  unfold posPart
  rw [List.map_append, List.map_append, List.filter_append, List.filter_append, List.map_map, List.map_map]
  have e1 : List.map (Int.toNat ∘ fun a : ℕ => (a : ℤ)) s = s := by simp [Function.comp_def]
  rw [e1, List.filter_eq_self.2 (by simpa using h), List.filter_eq_nil_iff.2 (by simp),
    List.filter_eq_nil_iff.2 (by simp), List.append_nil, List.append_nil]

end Labels

section Ring

variable {R T : Type} [CommRing R] [CommRing T] {n : ℕ}

theorem dv_map (ψ : R →+* T) (hψ : Function.Surjective ψ) {Λ : (Fin n → R) → Prop} {O : R → Prop} {O' : T → Prop}
    (hΛ : ∀ y, Λ y ↔ ∀ i, O' (ψ (y i))) (hO : ∀ x, O x ↔ O' (ψ x)) {e : R} {u : Fin n → R}
    {A : Matrix (Fin n) (Fin n) R} (h : GlobalTheory.DivDual.Dv Λ O e u A) :
    GlobalTheory.DivDual.Dv (fun z => ∀ i, O' (z i)) O' (ψ e) (fun i => ψ (u i)) (A.map ψ) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have s : ∀ z : Fin n → T, ∃ y : Fin n → R, z = ψ ∘ y := fun z => by
    choose y hy using fun i => hψ (z i)
    exact ⟨y, funext fun i => (hy i).symm⟩
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, ψ e • M.map ψ *ᵥ (ψ ∘ x) = ψ ∘ (e • M *ᵥ x) := fun M x =>
    funext fun i => by
      rw [Pi.smul_apply, ← RingHom.map_mulVec, Function.comp_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hu : ∀ z : Fin n → R, (fun i => ψ (u i) * (ψ ∘ z) i) = ψ ∘ fun i => u i * z i := fun z =>
    funext fun i => (map_mul ψ _ _).symm
  have sm : ∀ x : Fin n → R, ψ e • (ψ ∘ x) = ψ ∘ (e • x) := fun x => funext fun i => (map_mul ψ _ _).symm
  refine ⟨B.map ψ, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := s z
    rw [mv]
    exact (hΛ _).1 (h1 z fun i => (hO _).2 (hz i))
  · obtain ⟨y, rfl⟩ := s y
    obtain ⟨z, hz, e⟩ := h2 y ((hΛ _).2 hy)
    exact ⟨ψ ∘ z, fun i => (hO _).1 (hz i), by rw [mv, sm, e]⟩
  · obtain ⟨y, rfl⟩ := s y
    obtain ⟨z, hz, e⟩ := h3 y ((hΛ _).2 hy)
    exact ⟨ψ ∘ z, fun i => (hO _).1 (hz i), by rw [hu, mv, mv, e]⟩
  · obtain ⟨z, rfl⟩ := s z
    obtain ⟨y, hy, e⟩ := h4 z fun i => (hO _).2 (hz i)
    exact ⟨ψ ∘ y, (hΛ _).1 hy, by rw [hu, mv, mv, e]⟩

theorem supp_conj {ε : R} (c x : GL (Fin n) R) (h : ε • (x.1 - 1) = x.1 - 1) :
    ε • ((c⁻¹ * x * c).1 - 1) = (c⁻¹ * x * c).1 - 1 := by
  have e : (c⁻¹ * x * c).1 - 1 = (c⁻¹).1 * (x.1 - 1) * c.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]; rfl
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem int_of_away (S : Subring R) {ε : R} (hε : ε * ε = ε) (hεS : ε ∈ S) {a b c : Matrix (Fin n) (Fin n) R}
    (ha : ε • (a - 1) = a - 1) (hb : (1 - ε) • (b - 1) = b - 1) (hc : c = a * b ∨ c = b * a)
    (h : ∀ i j, (1 - ε) * c i j ∈ S) (i j : Fin n) : b i j ∈ S := by
  have e1 : (1 - ε) • a = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← sub_eq_zero, ← smul_sub, ← ha, smul_smul, sub_mul, one_mul, hε, sub_self, zero_smul]
  have e2 : (1 - ε) • c = (1 - ε) • b := by
    rcases hc with rfl | rfl
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
  have e3 : b = (1 - ε) • c + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [e2]
    ext i j
    have := congrFun (congrFun hb i) j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul] at this ⊢
    linear_combination -this
  rw [e3]
  refine add_mem (h i j) (mul_mem hεS ?_)
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end Ring

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_St_one (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔
    (∀ i j, x.1 i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (x⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  rw [← GlobalTheory.InertDoubleCoset.mem_range_iff]
  have : frGL (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = intGL F E n := by
    ext1 y; simp [frGL]
  unfold St
  rw [this]; rfl

theorem int_iff_of_St {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (∀ i, z i ∈ Formalism.L2.Herm.intAf F E) ↔ ∀ i, (x.1 *ᵥ z) i ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨h1, h2⟩ := (mem_St_one x).1 hx
  refine ⟨int_mulVec _ h1, fun hz => ?_⟩
  have := int_mulVec _ h2 hz
  rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this

end Std

section Host

open Formalism.L2.Col GlobalTheory.LevSplit GlobalTheory.IdemSupport

variable {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {Q : Pl D.host.E} {e : AE D}

theorem isFrame_of_base (hβ : IsBaseFrame V 1 Λ 1) : IsFrame (1 : GL (Fin V.rank) (Lev.EAf D)) (L0sub V) := by
  obtain ⟨h, -, -, h1, h2⟩ := hβ
  have : Λ = L0sub V := by
    ext x
    have a1 := h1 x
    have a2 := h2 x
    rw [Nat.cast_one, one_smul] at a1 a2
    exact ⟨a2, a1⟩
  exact this ▸ h

theorem mem_lamHat (hβ : IsBaseFrame V 1 Λ 1) (y : Fin V.rank → GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, swapAE D (y i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine (latHat_iff (L0sub V) y).trans ((isFrame_of_base hβ _).trans ?_)
  rw [inv_one, Units.val_one, one_mulVec]
  rfl

theorem mem_ksph (hβ : IsBaseFrame V 1 Λ 1) (g : GA D V) :
    g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧ finE V g ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) :=
  (ksph_iff V g).trans (and_congr_right fun _ => (mem_St_iff 1 (L0sub V) (isFrame_of_base hβ) (finE V g)).symm)

theorem idemOf_finSw (hP : IsPrimeIdem Q e e) : IdemOf D.host.F Q (finSw D e) := by
  refine ⟨?_, fun x hx => (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP x hx).trans (not_congr ?_)⟩
  · rw [← RingHom.map_mul, (GlobalTheory.HeckeDual.idem_of_isPrimeIdem hP).1]
  · refine (mem_intAE_iff _).trans ?_
    rw [show swapAE D (finPart D (e * incA D ((x : D.host.E)⁻¹))) = finSw D (e * incA D ((x : D.host.E)⁻¹)) from rfl,
      RingHom.map_mul, finSw_incA]

theorem dv_of_divAt (hβ : IsBaseFrame V 1 Λ 1) {ϖ : D.host.E} {d : List ℤ} {g : GA D V} (h : DivAt V e ϖ d g) :
    GlobalTheory.DivDual.Dv (fun z => ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (finSw D e) (fun i : Fin V.rank => iA D.host.F D.host.E (ϖ ^ d.getD i.1 0)) (finE V g).1 := by
  have hs : Function.Surjective (swapAE D) := (swp_bij (F := D.host.F) (E := D.host.E)).2
  have h1 := dv_map (swapAE D) hs (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D)
    (O' := fun x => x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (mem_lamHat hβ) (fun x => mem_intAE_iff x)
    ((GlobalTheory.DivDual.divAt_iff V e ϖ d g).1 h).2
  have e1 : (finMat D.sp.cm.sig V.gram g).map (swapAE D) = (finE V g).1 := rfl
  have e2 : swapAE D (finPart D e) = finSw D e := rfl
  have e3 : (fun i : Fin V.rank => swapAE D (finPart D (incA D (ϖ ^ d.getD i.1 0)))) =
      fun i : Fin V.rank => iA D.host.F D.host.E (ϖ ^ d.getD i.1 0) := funext fun i => finSw_incA _
  rw [e1, e2, e3] at h1
  exact h1

def inCoord (c : GL (Fin V.rank) (Lev.EAf D)) : GA D V →* GL (Fin V.rank) (Lev.EAf D) :=
  (MulAut.conj c⁻¹).toMonoidHom.comp (finE V)

theorem inCoord_apply (c : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) : inCoord c g = c⁻¹ * finE V g * c := by
  simp [inCoord]

variable {c : GL (Fin V.rank) (Lev.EAf D)}

theorem inCoord_supp {f : AE D} {g : GA D V} (h : SuppF V f g) :
    finSw D f • ((inCoord c g).1 - 1) = (inCoord c g).1 - 1 := by
  rw [inCoord_apply]
  exact supp_conj c _ (supp_fin V h)

theorem inCoord_mem_St (hc : c ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) (g : GA D V) :
    inCoord c g ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) ↔ finE V g ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := by
  rw [inCoord_apply, Subgroup.mul_mem_cancel_right _ hc, Subgroup.mul_mem_cancel_left _ (inv_mem hc)]

theorem quot_equiv_posPart (hβ : IsBaseFrame V 1 Λ 1) (hP : IsPrimeIdem Q e e) (hc : c ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)))
    {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) {d : List ℤ} {g : GA D V} (hg : SuppF V e g)
    (h : DivAt V e (ϖ : D.host.E) d g) (y : GL (Fin V.rank) (Lev.EAf D)) :
    Nonempty ((Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank) ⧸ (Formalism.UG.CS.globLat (y * inCoord c g) (Formalism.L2.Col.stdLat D.host.E V.rank) ⊓
      Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank)).comap (Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank)).subtype)
        ≃ₗ[𝓞 D.host.E] inType Q.asIdeal (posPart d)) := by
  have hD := (dv_of_divAt hβ h).mul (a := (c⁻¹).1) (a' := c.1) (b := c.1) (b' := (c⁻¹).1) c.inv_mul c.mul_inv
    (int_iff_of_St (inv_mem hc)) (int_iff_of_St hc)
  obtain ⟨e1⟩ := quot_equiv (idemOf_finSw hP) h1 h2 (fun i : Fin V.rank => d.getD i.1 0) y (inCoord c g)
    (inCoord_supp hg) (by rw [inCoord_apply]; exact hD)
  obtain ⟨e2⟩ := pi_equiv_posPart Q.asIdeal d h.1
  exact ⟨e1.trans e2⟩

theorem isInertNbr_of_divAt (hβ : IsBaseFrame V 1 Λ 1) (hP : IsPrimeIdem Q e e) (hc : c ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)))
    {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) {s : List ℕ} (hs : ∀ a ∈ s, 0 < a) {g : GA D V}
    (hg : SuppF V e g) (h : DivAt V e (ϖ : D.host.E) (labIn V.rank s) g) (y : GL (Fin V.rank) (Lev.EAf D)) :
    IsInertNbr Q.asIdeal s (Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank))
      (Formalism.UG.CS.globLat (y * inCoord c g) (Formalism.L2.Col.stdLat D.host.E V.rank)) := by
  have a1 := quot_equiv_posPart hβ hP hc h1 h2 hg h y
  have h' := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ g (GlobalTheory.HeckeDual.idem_of_isPrimeIdem hP).1 (IdemOf.unif_ne h2) h).1
  rw [dualLab_labIn] at h'
  have a2 := quot_equiv_posPart hβ hP hc h1 h2 ((suppGroup V e).inv_mem hg) h' (y * inCoord c g)
  rw [map_inv, mul_inv_cancel_right] at a2
  rw [posPart_labIn _ hs] at a1 a2
  exact ⟨a1, a2⟩

theorem exists_supp_globLat [NeZero V.rank] (hP : IsPrimeIdem Q e e)
    (hU : ∀ x ∈ UAd D.sp.cm V.rank, c * x * c⁻¹ ∈ UA D.sp.cm V.gram) {y : GL (Fin V.rank) (Lev.EAf D)}
    (hy : y ∈ UAd D.sp.cm V.rank) {N' : Submodule (𝓞 D.host.E) (Sp D.host.E V.rank)} (hl : Submodule.IsLattice D.host.E N')
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd D.host.E V.rank) N') {m : ℕ}
    (l1 : (Q.asIdeal ^ m) • Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank) ≤ N')
    (l2 : (Q.asIdeal ^ m) • N' ≤ Formalism.UG.CS.globLat y (Formalism.L2.Col.stdLat D.host.E V.rank)) :
    ∃ g : GA D V, SuppF V e g ∧ Formalism.UG.CS.globLat (y * inCoord c g) (Formalism.L2.Col.stdLat D.host.E V.rank) = N' := by
  obtain ⟨y', hy', rfl⟩ := unimodGenus_holds D.sp.cm V.rank N' hl hu
  have hI := idemOf_finSw hP
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 Q e e hP
  obtain ⟨u, -, hu⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ (hU _ (mul_mem (inv_mem hy) hy'))
  obtain ⟨g₁, g₂, s1, s2, rfl⟩ := exists_split V h0.1 h0.2.1 u
  have e1 : inCoord c g₁ * inCoord c g₂ = y⁻¹ * y' := by
    rw [← map_mul, inCoord_apply, hu]; group
  have e2 : (inCoord c g₂)⁻¹ * (inCoord c g₁)⁻¹ = y'⁻¹ * y := by
    rw [← _root_.mul_inv_rev, e1]; group
  have t1 := inCoord_supp (c := c) s1
  have t1' := inCoord_supp (c := c) ((suppGroup V e).inv_mem s1)
  have t2 := inCoord_supp (c := c) s2
  have t2' := inCoord_supp (c := c) ((suppGroup V (1 - e)).inv_mem s2)
  rw [map_inv] at t1' t2'
  rw [RingHom.map_sub, RingHom.map_one] at t2 t2'
  have hS : inCoord c g₂ ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := (mem_St_one _).2
    ⟨int_of_away _ hI.1 hI.mem t1 t2 (Or.inl (by rw [← e1, Units.val_mul])) (GlobalTheory.InertNbr.inv_mul_int_away Q _ hI m y' y l2),
     int_of_away _ hI.1 hI.mem t1' t2' (Or.inr (by rw [← e2, Units.val_mul])) (GlobalTheory.InertNbr.inv_mul_int_away Q _ hI m y y' l1)⟩
  refine ⟨g₁, s1, ?_⟩
  rw [← globLat_mul_St V.rank y' hS]
  congr 1
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, e1, mul_inv_cancel_left]

end Host

section Sum

open Formalism.L2.Col GlobalTheory.LevSplit GlobalTheory.IdemSupport GlobalTheory.SplitHeckeAdj

variable {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {Q : Pl D.host.E} {e : AE D}
  {c : GL (Fin V.rank) (Lev.EAf D)}

theorem decoOf_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] (ST SG : Finset (Pl E)) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ UAd hc n) : (decoOf ST SG x).1 = decoRaw ST SG x := by
  unfold decoOf
  rw [dif_pos (decorated_lattice_exists hc n ST SG x hx)]

theorem sum_reps [NeZero V.rank] (hβ : IsBaseFrame V 1 Λ 1) (hP : IsPrimeIdem Q e e)
    (hc : c ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)))
    (hU : ∀ x, x ∈ UAd D.sp.cm V.rank ↔ c * x * c⁻¹ ∈ UA D.sp.cm V.gram) {SG : Finset (Pl D.host.E)} (hQ : Q ∉ SG)
    {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) {s : List ℕ} (hs : InertTypeOk V.rank s)
    {α : GA D V} (hα : SuppF V e α) (hD : DivAt V e (ϖ : D.host.E) (labIn V.rank s) α) {R : Finset (GA D V)}
    (hR : ∀ γ ∈ R, SuppF V e γ) (hrep : IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V e k} α R)
    {y : GL (Fin V.rank) (Lev.EAf D)} (hy : y ∈ UAd D.sp.cm V.rank) {M : Type} [AddCommMonoid M]
    (ψ : DecoSet D.host.E V.rank ∅ SG → M) :
    ∑ γ ∈ R, ψ (decoOf ∅ SG (y * inCoord c γ)) = ∑ d ∈ (decoOf ∅ SG y).inertNb Q.asIdeal s, ψ d := by
  have hI := idemOf_finSw hP
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 Q e e hP
  have hϖ := IdemOf.unif_ne h2
  have hin : ∀ g : GA D V, inCoord c g ∈ UAd D.sp.cm V.rank := fun g => by
    rw [hU, inCoord_apply]
    have : c * (c⁻¹ * finE V g * c) * c⁻¹ = finE V g := by group
    rw [this]
    exact finE_mem_UA V g
  have hval : ∀ g : GA D V, (decoOf ∅ SG (y * inCoord c g)).1 = decoRaw ∅ SG (y * inCoord c g) := fun g =>
    decoOf_val D.sp.cm ∅ SG (mul_mem hy (hin g))
  have hval0 := decoOf_val D.sp.cm ∅ SG hy
  have hdeco : ∀ g : GA D V, SuppF V e g → (decoRaw ∅ SG (y * inCoord c g)).f = (decoRaw ∅ SG y).f ∧
      (decoRaw ∅ SG (y * inCoord c g)).be = (decoRaw ∅ SG y).be := fun g hg =>
    GlobalTheory.InertNbr.decoRaw_mul_idem ∅ SG Q _ hI (Finset.notMem_empty Q) hQ y _ (inCoord_supp hg)
  have hdiv : ∀ γ ∈ R, DivAt V e (ϖ : D.host.E) (labIn V.rank s) γ := fun γ hγ => by
    obtain ⟨-, k₁, a₁, k₂, a₂, rfl⟩ := hrep.1 γ hγ
    exact (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ α h0.1 hϖ hD).2 k₁ a₁.1 k₂ a₂.1
  refine Finset.sum_bij (fun γ _ => decoOf ∅ SG (y * inCoord c γ)) (fun γ hγ => ?_) (fun γ hγ γ' hγ' h => ?_)
    (fun d hd => ?_) fun _ _ => rfl
  · rw [DecoSet.mem_inertNb Q.ne_bot]
    refine ⟨?_, ?_, ?_⟩ <;> rw [hval, hval0]
    · exact isInertNbr_of_divAt hβ hP hc h1 h2 hs.2.1 (hR γ hγ) (hdiv γ hγ) y
    · exact (hdeco γ (hR γ hγ)).1
    · exact (hdeco γ (hR γ hγ)).2
  · have h3 : decoRaw ∅ SG (y * inCoord c γ) = decoRaw ∅ SG (y * inCoord c γ') := by
      rw [← hval, ← hval]; exact congrArg Subtype.val h
    have h4 := congruence_subgroup_le_stabilizer _ _ _ (principal_le_congruence_subgroup _ _ _ _
      (mem_principal_of_same_decoration D.sp.cm V.rank ∅ SG (mul_mem hy (hin γ)) (mul_mem hy (hin γ')) h3))
    have e1 : (y * inCoord c γ)⁻¹ * (y * inCoord c γ') = inCoord c (γ⁻¹ * γ') := by
      rw [map_mul, map_inv]; group
    rw [e1, inCoord_mem_St hc] at h4
    have s1 : SuppF V e (γ⁻¹ * γ') := (suppGroup V e).mul_mem ((suppGroup V e).inv_mem (hR γ hγ)) (hR γ' hγ')
    have s0 : SuppF V e 1 := (suppGroup V e).one_mem
    refine (hrep.2 γ' (hrep.1 γ' hγ').2).unique ⟨hγ, (mem_ksph hβ _).2 ⟨h0.2.2.1 _ s1, h4⟩, s1⟩ ⟨hγ', ?_⟩
    rw [inv_mul_cancel]
    exact ⟨GlobalTheory.InertDoubleCoset.one_mem_KsphC V, s0⟩
  · rw [DecoSet.mem_inertNb Q.ne_bot] at hd
    obtain ⟨d1, d2, d3⟩ := hd
    rw [hval0] at d1 d2 d3
    obtain ⟨g, hg, hN⟩ := exists_supp_globLat (c := c) hP (fun x hx => (hU x).1 hx) hy d.2.lat d.2.uni d1.smul_le.1 d1.smul_le.2
    obtain ⟨l, hl, hlD⟩ := GlobalTheory.SphLabelOps.exists_divAt V h0.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP) h1 h2 g
    have hself : dualLab l = l := ((GlobalTheory.LabChar.labels_char V Q l).1
      (GlobalTheory.SphLabelOps.isLab_of_divAt hP h1 h2 hl hg hlD)).2.2 (GlobalTheory.LabChar.fixed_of_tie hP)
    obtain ⟨q1⟩ := quot_equiv_posPart hβ hP hc h1 h2 hg hlD y
    rw [hN] at q1
    obtain ⟨q2⟩ := d1.1
    have hps : posPart l = s :=
      GlobalTheory.InertDivUniq.inType_exps_unique Q _ _ (posPart_pairwise hl) (posPart_pos l) hs.1 hs.2.1 ⟨q1.symm.trans q2⟩
    obtain rfl : l = labIn V.rank s := eq_of_posPart_eq hl (labIn_pairwise _ hs.1) (hlD.1.trans hD.1.symm) hself
      (dualLab_labIn _ s) (hps.trans (posPart_labIn _ hs.2.1).symm)
    obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V Q e hP
      (GlobalTheory.SphLabelOps.exists_real_unif D Q) α hα).2.2 ϖ ϖ _ g h1 h2 h1 h2 hl hg hD hlD
    obtain ⟨γ, ⟨hγ, hK⟩, -⟩ := hrep.2 g ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩
    refine ⟨γ, hγ, Subtype.ext ?_⟩
    rw [hval]
    refine Deco.ext ?_ ((hdeco γ (hR γ hγ)).1.trans d2.symm) ((hdeco γ (hR γ hγ)).2.trans d3.symm)
    rw [← hN, ← globLat_mul_St V.rank (y * inCoord c g) ((inCoord_mem_St hc _).2 ((mem_ksph hβ _).1 hK.1).2)]
    show Formalism.UG.CS.globLat _ _ = _
    congr 1
    rw [map_mul, map_inv]; group

theorem conjPl_eq_of_conjP {Q : Pl D.host.E} (h : conjPrime₂ Q = Q) : Formalism.DivisionValues.conjPl Q = Q := by
  rw [GlobalTheory.LabChar.conjPl_eq_cP]
  exact h

theorem isConjPl_self {Q : Pl D.host.E} (h : conjPrime₂ Q = Q) : Formalism.IndefR.Lev.IsConjPl Q Q := by
  have := isConjPl_conj Q
  rwa [conjPl_eq_of_conjP h] at this

theorem exists_hecke (V : HSp D) {n : ℕ} [NeZero n] (h : n = V.rank) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V 1 Λ 1) (Q : Pl D.host.E) (hQc : conjPrime₂ Q = Q)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) {SG : Finset (Pl D.host.E)} (hQ : Q ∉ SG)
    (A k : GL (Fin n) (Lev.EAf D)) (hA : A ∈ St (1 : GL (Fin n) (Lev.EAf D)))
    (hAU : ∀ x, x ∈ UAd D.sp.cm n ↔ LiftBrg.castGL h (A * x * A⁻¹) ∈ UA D.sp.cm V.gram)
    (hkU : k ∈ UAd D.sp.cm n) (hk : k ∈ St (1 : GL (Fin n) (Lev.EAf D))) (s : List ℕ) (hs : InertTypeOk V.rank s) :
    ∃ (x : Bridge.Gf V) (R : Finset (Bridge.Gf V)), IsLabElt V Q (labIn V.rank s) x ∧ (∀ a ∈ R, IsLocElt V Q a) ∧
      Bridge.IsDC (levEnv V 1 L).J x R ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : DecoSet D.host.E n ∅ SG → M) (g : Bridge.Gf V),
        ∑ a ∈ R, ψ (decoOf ∅ SG (A⁻¹ * LiftBrg.castGL h.symm (Formalism.UG.bc (swapAE D) ((g * a : Bridge.Gf V) : GL (Fin V.rank) _)) * A * k)) =
          ∑ d ∈ (decoOf ∅ SG (A⁻¹ * LiftBrg.castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) * A * k)).inertNb
            Q.asIdeal s, ψ d := by
  classical
  subst h
  have hcast : ∀ x : GL (Fin V.rank) (Lev.EAf D), LiftBrg.castGL (rfl : V.rank = V.rank) x = x := fun x => by
    ext i j
    rfl
  simp only [hcast] at hAU ⊢
  have hQc' := conjPl_eq_of_conjP hQc
  obtain ⟨e, f, hP⟩ := (supported_group_and_prime_idempotents V).2.1 Q
  obtain rfl := GlobalTheory.LabChar.eq_of_fixed V hP hQc'
  have hN := ((supported_group_and_prime_idempotents V).2.2.1 Q f f hP).2.2.1
  obtain ⟨x, ϖ, hϖ, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D Q
  obtain ⟨α, hα, hD⟩ := GlobalTheory.InertExist.exists_suppF_divAt V Q f x ϖ (labIn V.rank s) hP hϖ h1 h2 (labIn_length hs.2.2)
    (dualLab_labIn _ s)
  obtain ⟨R, hR, hrep⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V Q f hP ⟨x, ϖ, hϖ, h1, h2⟩ α hα).2.1
  have hoff' : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP Q := fun PP hPP =>
    ⟨hoff PP hPP, fun hc => hoff PP hPP (by
      have e1 := eq_conj_of_isConjPl hc
      rw [← hQc', e1, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl])⟩
  have hlev := GlobalTheory.DefiniteOps.local_level V 1 Λ L hβ Q hoff' hP
  refine ⟨fin V α, R.image (fin V), ⟨f, f, ϖ, α, hP, h1, h2, hN α hα, rfl, hα, hD⟩, fun a ha => ?_,
    GlobalTheory.DefiniteOps.isDC_image (fin V) _ (suppGroup V f) _ hlev.2.2 hlev.1 α hα R hR (fun γ hγ => (hrep.1 γ hγ).2) hrep.2,
    fun M _ ψ g => ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨f, f, γ, hP, hN γ (hR γ hγ), rfl, hR γ hγ⟩
  · obtain ⟨g, -, rfl⟩ := fin_lift V g
    have hU : ∀ x, x ∈ UAd D.sp.cm V.rank ↔ (A * k) * x * (A * k)⁻¹ ∈ UA D.sp.cm V.gram := fun x => by
      have e1 : (A * k) * x * (A * k)⁻¹ = A * (k * x * k⁻¹) * A⁻¹ := by group
      rw [e1, ← hAU, Subgroup.mul_mem_cancel_right _ (inv_mem hkU), Subgroup.mul_mem_cancel_left _ hkU]
    have hy : A⁻¹ * finE V g * A * k ∈ UAd D.sp.cm V.rank := by
      refine mul_mem ((hAU _).2 ?_) hkU
      have e1 : A * (A⁻¹ * finE V g * A) * A⁻¹ = finE V g := by group
      rw [e1]
      exact finE_mem_UA V g
    rw [Finset.sum_image fun a ha b hb => fin_inj V (hN a (hR a ha)) (hN b (hR b hb))]
    refine Eq.trans (Finset.sum_congr rfl fun γ _ => ?_)
      (sum_reps hβ hP (mul_mem hA hk) hU hQ h1 h2 hs hα hD hR hrep hy ψ)
    rw [← map_mul]
    show ψ (decoOf ∅ SG (A⁻¹ * finE V (g * γ) * A * k)) = _
    congr 2
    rw [map_mul, inCoord_apply]
    group

end Sum

theorem inert_neighbours : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ q : ↑((famR X I hX U Xg tr).okI t) × List ℕ, Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 →
    ∃ (x : Bridge.Gf (Vc X.toD7 i)) (R : Finset (Bridge.Gf (Vc X.toD7 i))),
      IsLabElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank q.2) x ∧
      (∀ a ∈ R, IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 a) ∧
      Bridge.IsDC (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J x R ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e := by
  intro X px I hX U Xg tr L eG _ _ hL _ cV i t A k hF q hs
  obtain ⟨m, hm⟩ := hL.is.βV i
  rw [one_pow] at hm
  have hβ := hL.beta.1 i
  have hQc : Formalism.L2.Col.conjPrime₂ (q.1.1 : PlI X.B px).1 = (q.1.1 : PlI X.B px).1 := (q.1.1 : PlI X.B px).2.1
  have hQ : (q.1.1 : PlI X.B px).1 ∉ LiftBrg.sgL X I U t := fun h => q.1.2 (Or.inr h)
  have hoff : ∀ PP, PP ∈ (L.datVt i t).Pg ∨ PP ∈ (L.datVt i t).Q → PP ≠ (q.1.1 : PlI X.B px).1 := by
    rintro PP (h | h) rfl
    · have h' : (q.1.1 : PlI X.B px).1 ∈ L.Pg := h
      rw [hL.Pg] at h'
      exact (q.1.1 : PlI X.B px).2.2.2 (Or.inr h')
    · refine (hL.is.Q_pl t _ h).2 _ h ?_
      exact isConjPl_self (D := X.toD7) hQc
  rw [hβ] at hm
  have key := exists_hecke (Vc X.toD7 i) (LiftBrg.rkEq X i) (L.ΛV i) (L.datVt i t) hm _ hQc hoff hQ A k hF.2.1 hF.2.2.1
    hF.2.2.2.1 hF.2.2.2.2.1 q.2 hs
  rw [← hβ] at key
  exact key

end GlobalTheory.InertNbr
