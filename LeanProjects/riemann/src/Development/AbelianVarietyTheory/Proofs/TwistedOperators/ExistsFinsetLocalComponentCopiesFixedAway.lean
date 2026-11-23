import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem apply_comm (φ : π.IntertwiningMap ρ) (g : G) (n : N) : φ.toLinearMap (π g n) = ρ g (φ.toLinearMap n) :=
  LinearMap.congr_fun (φ.isIntertwining' g) n

theorem isSemisimple_of_isotypic (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) : ρ.IsSemisimpleRepresentation := by
  haveI := hπ
  have hs : π.IsSemisimpleRepresentation :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule π).2 inferInstance
  exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G X ρ (π.IntertwiningMap ρ) (fun _ => N) (fun _ => π)
    (fun φ => φ.toLinearMap) (fun _ => hs) (fun φ g x => apply_comm φ g x) h

theorem stable_biSup (s : Finset (π.IntertwiningMap ρ)) (g : G) :
    ∀ x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, ρ g x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro x hx
  have : (⨆ φ ∈ s, LinearMap.range φ.toLinearMap) ≤ (⨆ φ ∈ s, LinearMap.range φ.toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun φ hφ => ?_
    rintro _ ⟨n, rfl⟩
    rw [Submodule.mem_comap, ← apply_comm]
    exact Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ ⟨_, rfl⟩)
  exact this hx

theorem exists_intertwining_le (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) (C : Subrepresentation ρ)
    (hC : C ≠ ⊥) : ∃ ψ : π.IntertwiningMap ρ, Function.Injective ψ ∧ ∀ n, ψ n ∈ C.toSubmodule := by
  haveI := hπ
  haveI := isSemisimple_of_isotypic hπ h
  obtain ⟨C1, hc⟩ := exists_isCompl C
  have hc' : IsCompl C.toSubmodule C1.toSubmodule :=
    IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hc.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hc.sup_eq_top)
  let P : X →ₗ[ℂ] X := C.toSubmodule.subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hc'
  have hPl : ∀ a ∈ C.toSubmodule, P a = a := fun a ha =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc' ⟨a, ha⟩)
  have hPr : ∀ b ∈ C1.toSubmodule, P b = 0 := fun b hb =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc' ⟨b, hb⟩)
  have hPi : ∀ g x, P (ρ g x) = ρ g (P x) := fun g x => by
    have hx : x ∈ C.toSubmodule ⊔ C1.toSubmodule := by rw [hc'.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, map_add, hPl a ha, hPr b hb, hPl _ (C.apply_mem_toSubmodule g ha),
      hPr _ (C1.apply_mem_toSubmodule g hb), add_zero, add_zero]
  have hPm : ∀ x, P x ∈ C.toSubmodule := fun x => by simp [P]
  obtain ⟨c, hc0, hcne⟩ : ∃ c ∈ C.toSubmodule, c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hC (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun x hx => hn x hx))
  by_contra hno
  push_neg at hno
  have hall : ∀ φ : π.IntertwiningMap ρ, LinearMap.range φ.toLinearMap ≤ LinearMap.ker P := by
    intro φ
    let ψ : π.IntertwiningMap ρ := ⟨P ∘ₗ φ.toLinearMap, fun g => LinearMap.ext fun n => by
      simp only [LinearMap.comp_apply]
      rw [apply_comm φ g n, hPi]⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero ψ with hi | h0
    · obtain ⟨n, hn⟩ := hno ψ hi
      exact absurd (hPm _) hn
    · rintro _ ⟨n, rfl⟩
      exact DFunLike.congr_fun h0 n
  have : c ∈ LinearMap.ker P := by
    have h1 : c ∈ isoPartAlg π ρ := by rw [h]; trivial
    exact (iSup_le hall) h1
  exact hcne ((hPl c hc0).symm.trans this)

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem le_biSup_of_fixed (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) {v : N} (hv : v ≠ 0) (Y : Submodule ℂ X)
    (hY : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y) (s : Finset (π.IntertwiningMap ρ))
    (hF : ∀ x ∈ Y, (∀ g, π g v = v → ρ g x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) :
    Y ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  haveI := isSemisimple_of_isotypic hπ h
  let A : Subrepresentation ρ := ⟨Y ⊓ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, fun g x hx =>
    ⟨hY g x hx.1, stable_biSup s g x hx.2⟩⟩
  obtain ⟨C0, hc⟩ := exists_isCompl A
  let C : Subrepresentation ρ := ⟨Y ⊓ C0.toSubmodule, fun g x hx => ⟨hY g x hx.1, C0.apply_mem_toSubmodule g hx.2⟩⟩
  have hC : C = ⊥ := by
    by_contra hne
    obtain ⟨ψ, hi, hm⟩ := exists_intertwining_le hπ h C hne
    have hx0 : ψ v ≠ 0 := fun e => hv (hi (e.trans (map_zero ψ).symm))
    have hxY : ψ v ∈ Y := (hm v).1
    have hxM := hF _ hxY fun g hg => by rw [← ψ.isIntertwining, hg]
    have h1 : ψ v ∈ (A ⊓ C0).toSubmodule := ⟨⟨hxY, hxM⟩, (hm v).2⟩
    rw [hc.inf_eq_bot] at h1
    exact hx0 h1
  intro y hy
  have h2 : y ∈ (A ⊔ C0).toSubmodule := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 h2
  have hcY : c ∈ Y := by simpa using Y.sub_mem hy ha.1
  have hcC : c ∈ C.toSubmodule := ⟨hcY, hc'⟩
  rw [hC] at hcC
  have hc0 : c = 0 := hcC
  rw [hc0, add_zero]
  exact ha.2

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

variable {D : D7} {V : HSp D} (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  proj_emb_self D.sp.cm.sig V.gram u x

theorem commute_locFin (x : Gv V u) {k : GfC V} (hk : finLoc V u k = 1) : Commute (locFin V u x) k :=
  Subtype.ext (commute_emb D.sp.cm.sig V.gram x hk).eq

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val

theorem continuous_locFin : Continuous (locFin V u) :=
  (continuous_emb D.sp.cm.sig V.gram u).subtype_mk _

noncomputable def away : GfC V →* GfC V where
  toFun k := k * (locFin V u (finLoc V u k))⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hb : finLoc V u (b * (locFin V u (finLoc V u b))⁻¹) = 1 := by
      rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]
    have hc := (commute_locFin u (finLoc V u a) hb).inv_left
    simp only [map_mul, mul_inv_rev]
    rw [mul_assoc a _ (b * _), hc.eq]
    simp only [mul_assoc]

theorem finLoc_away (k : GfC V) : finLoc V u (away u k) = 1 := by
  show finLoc V u (k * (locFin V u (finLoc V u k))⁻¹) = 1
  rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]

theorem away_mul (k : GfC V) : away u k * locFin V u (finLoc V u k) = k := by
  show k * (locFin V u (finLoc V u k))⁻¹ * locFin V u (finLoc V u k) = k
  group

theorem continuous_away : Continuous (away (V := V) u) :=
  continuous_id.mul (((continuous_locFin u).comp (continuous_finLoc u)).inv)

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

theorem exists_finset_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro D V u W _ _ σ hσa N _ _ π hπ hπa hloc K hK
  have hiso : IsIsotypicAlg π (σ.comp (locFin V u)) := hloc
  obtain ⟨v, hv⟩ : ∃ v : N, v ≠ 0 := by
    by_contra hn
    push_neg at hn
    haveI : Subsingleton N := ⟨fun a b => (hn a).trans (hn b).symm⟩
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  let St : Subgroup (Gv V u) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        show π a⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSt : IsOpen (St : Set (Gv V u)) := hπa.1 v
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  let K2 : Subgroup (GfC V) := K0 ⊓ St.comap (finLoc V u) ⊓ K.comap (away u)
  have hK2o : IsOpen (K2 : Set (GfC V)) :=
    (hK0o.inter (hSt.preimage (continuous_finLoc u))).inter (hK.preimage (continuous_away u))
  have hK2c : IsCompact (K2 : Set (GfC V)) :=
    hK0c.of_isClosed_subset (K2.isClosed_of_isOpen hK2o) fun k hk => hk.1.1
  haveI := hσa.2 K2 hK2o hK2c
  let Y : Submodule ℂ W := GlobalTheory.PRep.fixed σ (K ⊓ (finLoc V u).ker)
  have hmemY : ∀ x, x ∈ Y ↔ ∀ k ∈ K, finLoc V u k = 1 → σ k x = x := by
    intro x
    rw [GlobalTheory.CuspDec.mem_fixed]
    exact ⟨fun h k hk h1 => h k ⟨hk, h1⟩, fun h k hk => h k hk.1 hk.2⟩
  have hY : ∀ g, ∀ x ∈ Y, σ.comp (locFin V u) g x ∈ Y := by
    intro g x hx
    rw [hmemY] at hx ⊢
    intro k hk h1
    show σ k (σ (locFin V u g) x) = σ (locFin V u g) x
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin u g h1).eq, map_mul, Module.End.mul_apply, hx k hk h1]
  let F : Submodule ℂ W := Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) St
  have hFle : F ≤ GlobalTheory.PRep.fixed σ K2 := by
    intro y hy
    rw [GlobalTheory.CuspDec.mem_fixed]
    intro k hk
    have h1 : σ (locFin V u (finLoc V u k)) y = y := (GlobalTheory.CuspDec.mem_fixed.1 hy.2) _ hk.1.2
    have h2 : σ (away u k) y = y := (hmemY y).1 hy.1 _ hk.2 (finLoc_away u k)
    rw [← away_mul u k, map_mul, Module.End.mul_apply, h1, h2]
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFle
  have hFfg : F.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ ((Submodule.fg_iff_compact F).1 hFfg)
    (fun φ : π.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range φ.toLinearMap)
    (le_of_le_of_eq le_top hiso.symm)
  refine ⟨s, fun x hx => le_biSup_of_fixed hπ hiso hv Y hY s (fun y hy hfix => hs ⟨hy, ?_⟩) ((hmemY x).2 hx)⟩
  exact GlobalTheory.CuspDec.mem_fixed.2 fun k hk => hfix k hk

end GlobalTheory.FinMultAway
