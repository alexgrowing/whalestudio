import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MidJacquet

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def tupleRep (π : Representation ℂ G V) (m : ℕ) : Representation ℂ G (Fin m → V) where
  toFun g := LinearMap.pi fun j => π g ∘ₗ LinearMap.proj j
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem tupleRep_apply (π : Representation ℂ G V) (m : ℕ) (g : G) (u : Fin m → V) :
    tupleRep π m g u = fun j => π g (u j) := rfl

theorem isSmooth_tupleRep [TopologicalSpace G] {π : Representation ℂ G V} (hπ : IsSmooth π) (m : ℕ) :
    IsSmooth (tupleRep π m) := by
  intro u
  have e : {g : G | tupleRep π m g u = u} = ⋂ j, {g : G | π g (u j) = u j} := by
    ext g
    simp [funext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun j => hπ (u j)

theorem map_eq_zero_of_compact [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V}
    (hπ : IsSmooth π) {m : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] (Λ : (Fin m → V) →ₗ[ℂ] X)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (u : Fin m → V)
    (hu : ∀ h ∈ H, Λ (fun j => π h (u j)) = Λ u) (hk : ∀ j, u j ∈ twKer π H 1) : Λ u = 0 := by
  let f : (Fin m → V) →ₗ[ℂ] X × (Fin m → V ⧸ twKer π H 1) :=
    Λ.prod (LinearMap.pi fun j => (twKer π H 1).mkQ ∘ₗ LinearMap.proj j)
  obtain ⟨v, hv, hfv⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq (isSmooth_tupleRep hπ m) hH f u (by
    intro h hh
    refine Prod.ext (hu h hh) (funext fun j => ?_)
    exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh (u j)))
  have h1 : Λ v = Λ u := congrArg Prod.fst hfv
  have h2 : ∀ j, v j = 0 := by
    intro j
    have hq : (twKer π H 1).mkQ (v j) = (twKer π H 1).mkQ (u j) := congrFun (congrArg Prod.snd hfv) j
    refine GlobalTheory.IwahoriInj.eq_zero_of_fixed hπ hH ?_ ?_
    · refine GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => ?_
      exact congrFun (GlobalTheory.IwahoriInj.mem_fixed (π := tupleRep π m).1 hv h hh) j
    · have h0 : (twKer π H 1).mkQ (u j) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (hk j)
      exact (Submodule.Quotient.mk_eq_zero _).1 (hq.trans h0)
  have h3 : v = 0 := funext h2
  rw [← h1, h3, map_zero]

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] {s : ℕ} {d : Fin s → ℕ}

theorem map_eq_zero_of_unipRad (e : (Σ a, Fin (d a)) ≃ ι) {π : Representation ℂ (GL ι k) V}
    (hπ : IsSmooth π) {m : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] (Λ : (Fin m → V) →ₗ[ℂ] X)
    (u : Fin m → V) (hu : ∀ g ∈ unipRad k e, Λ (fun j => π g (u j)) = Λ u)
    (hk : ∀ j, u j ∈ twKer π (unipRad k e) 1) : Λ u = 0 := by
  classical
  have hN : unipRad k e = GlobalTheory.InertSupp.unipOf k fun i => ((blk e i).val : ℤ) :=
    GlobalTheory.InertSupp.unipRad_eq_unipOf k fun i j => by simp
  choose S hS hSH using fun j => GlobalTheory.JacquetExact.exists_finset_of_mem_twKer (hk j)
  obtain ⟨H, hle, hH, hSH'⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k ι _ (Finset.univ.biUnion S) (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    rw [← hN]
    exact hS j x hj)
  refine map_eq_zero_of_compact hπ Λ hH u (fun h hh => hu h (hN ▸ hle hh)) fun j =>
    hSH j H fun x hx => hSH' x (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hx⟩)

end Local

end GlobalTheory.MidJacquet

namespace GlobalTheory.MidJacquet

theorem exists_subquotient_jacU_intertwining : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n l d : ℕ) (hld : l + d ≤ n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π →
    ∀ (m : ℕ) (U : Submodule ℂ (Fin m → V)),
      (∀ g : GL (Fin d) k, ∀ u ∈ U, (fun j => π (GlobalTheory.SmGL.leviEmb k (tripPlace hld) (midHom k l d n g)) (u j)) ∈ U) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin d) k) W) (Λ : (Fin m → V) →ₗ[ℂ] W),
      (∃ u ∈ U, Λ u ≠ 0) →
      (∀ g ∈ GlobalTheory.SmGL.unipRad k (tripPlace hld), ∀ u ∈ U, Λ (fun j => π g (u j)) = Λ u) →
      (∀ g : GL (Fin d) k, ∀ u ∈ U,
        Λ (fun j => π (GlobalTheory.SmGL.leviEmb k (tripPlace hld) (midHom k l d n g)) (u j)) = ρ g (Λ u)) →
      ∃ (W' : Type) (_ : AddCommGroup W') (_ : Module ℂ W') (Q : Representation ℂ (GL (Fin d) k) W'),
        IsSubquotient Q ((jacU (tripPlace hld) π).comp (midHom k l d n)) ∧ ∃ f : Q.IntertwiningMap ρ, f ≠ 0 := by
  intro k _ _ _ _ n l d hld V _ _ π hπ m U hU W _ _ ρ Λ hne hinv hequiv
  classical
  set e := tripPlace hld with he
  set N := unipRad k e with hNdef
  set τ := (jacU e π).comp (midHom k l d n) with hτ

  let A : ℕ → Submodule ℂ (Fin m → V) := fun t =>
    U ⊓ ⨅ (i : Fin m) (_ : t ≤ i.val), (twKer π N 1).comap (LinearMap.proj i)
  have memA : ∀ t u, u ∈ A t ↔ u ∈ U ∧ ∀ i : Fin m, t ≤ i.val → u i ∈ twKer π N 1 := by
    intro t u
    simp [A, Submodule.mem_iInf]
  have hP : ∃ t, ∃ u ∈ A t, Λ u ≠ 0 := by
    obtain ⟨u, hu, hΛ⟩ := hne
    exact ⟨m, u, (memA m u).2 ⟨hu, fun i hi => absurd i.2 (not_lt.2 hi)⟩, hΛ⟩
  have h0 : ∀ u ∈ A 0, Λ u = 0 := by
    intro u hu
    rw [memA] at hu
    exact map_eq_zero_of_unipRad e hπ Λ u (fun g hg => hinv g hg u hu.1) fun j => hu.2 j (Nat.zero_le _)
  set t₀ := Nat.find hP with ht₀
  obtain ⟨u₀, hu₀, hΛ₀⟩ := Nat.find_spec hP
  have ht₀0 : t₀ ≠ 0 := by
    intro h
    exact hΛ₀ (h0 u₀ (by rw [← h]; exact hu₀))
  have ht₀m : t₀ ≤ m := Nat.find_min' hP ⟨u₀, (memA m u₀).2 ⟨((memA _ _).1 hu₀).1,
    fun i hi => absurd i.2 (not_lt.2 hi)⟩, hΛ₀⟩
  have hmin : ∀ u ∈ A (t₀ - 1), Λ u = 0 := by
    intro u hu
    by_contra h
    exact Nat.find_min hP (by omega : t₀ - 1 < t₀) ⟨u, hu, h⟩
  let jj : Fin m := ⟨t₀ - 1, by omega⟩
  let B := A t₀
  let L : B →ₗ[ℂ] Jacquet π N := (twKer π N 1).mkQ ∘ₗ LinearMap.proj jj ∘ₗ B.subtype
  have hL : ∀ b : B, L b = Submodule.Quotient.mk ((b : Fin m → V) jj) := fun b => rfl
  have hker : LinearMap.ker L ≤ LinearMap.ker (Λ ∘ₗ B.subtype) := by
    intro b hb
    rw [LinearMap.mem_ker] at hb ⊢
    have hb1 : (b : Fin m → V) jj ∈ twKer π N 1 := (Submodule.Quotient.mk_eq_zero _).1 hb
    have hb2 := (memA t₀ b).1 b.2
    refine hmin b ((memA _ _).2 ⟨hb2.1, fun i hi => ?_⟩)
    rcases Nat.eq_or_lt_of_le hi with h | h
    · have : i = jj := Fin.ext h.symm
      rw [this]; exact hb1
    · exact hb2.2 i (by omega)
  let φ : LinearMap.range L →ₗ[ℂ] W :=
    (LinearMap.ker L).liftQ (Λ ∘ₗ B.subtype) hker ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ b : B, φ ⟨L b, LinearMap.mem_range_self L b⟩ = Λ b := by
    intro b
    simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
      Submodule.coe_subtype]

  have hstab : ∀ (g : GL (Fin d) k) (b : Fin m → V), b ∈ B →
      (fun j => π (leviEmb k e (midHom k l d n g)) (b j)) ∈ B := by
    intro g b hb
    rw [memA] at hb ⊢
    refine ⟨hU g b hb.1, fun i hi => ?_⟩
    exact twKer_le_comap π N _ (leviEmb_mem_normalizer k e _) (hb.2 i hi)
  have hτL : ∀ (g : GL (Fin d) k) (b : B),
      τ g (L b) = L ⟨_, hstab g b b.2⟩ := fun g b => rfl
  let S : Subrepresentation τ :=
    { toSubmodule := LinearMap.range L
      apply_mem_toSubmodule := by
        rintro g _ ⟨b, rfl⟩
        rw [hτL]
        exact LinearMap.mem_range_self L _ }
  let f : S.toRepresentation.IntertwiningMap ρ :=
    ⟨φ, fun g => by
      ext x
      obtain ⟨_, b, rfl⟩ := x
      have e1 : S.toRepresentation g ⟨L b, LinearMap.mem_range_self L b⟩ =
          ⟨L ⟨_, hstab g b b.2⟩, LinearMap.mem_range_self L _⟩ := Subtype.ext (hτL g b)
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [e1, hφ, hφ]
      exact hequiv g b ((memA _ _).1 b.2).1⟩
  refine ⟨S.toSubmodule, inferInstance, inferInstance, S.toRepresentation,
    ⟨S, .id _, Function.surjective_id⟩, f, fun hf => hΛ₀ ?_⟩
  have := congrArg (fun F : S.toRepresentation.IntertwiningMap ρ =>
    F ⟨L ⟨u₀, hu₀⟩, LinearMap.mem_range_self L _⟩) hf
  have e2 : f ⟨L ⟨u₀, hu₀⟩, LinearMap.mem_range_self L _⟩ = Λ u₀ := hφ ⟨u₀, hu₀⟩
  rw [← e2, this]
  rfl

end GlobalTheory.MidJacquet
