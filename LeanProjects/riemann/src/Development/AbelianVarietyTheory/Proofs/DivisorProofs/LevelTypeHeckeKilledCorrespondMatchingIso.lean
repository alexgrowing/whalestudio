import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqTrans

theorem asAlg_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (x : MonoidAlgebra ℂ H) :
    Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) x =
      ρ.asAlgebraHom (MonoidAlgebra.domCongr ℂ ℂ e x) := by
  have : Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) =
      ρ.asAlgebraHom.comp (MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · exact Subsingleton.elim _ _
  rw [this]; rfl

theorem killed_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (I : Set (MonoidAlgebra ℂ H)) (I' : Set (MonoidAlgebra ℂ H'))
    (h1 : ∀ x ∈ I, MonoidAlgebra.domCongr ℂ ℂ e x ∈ I')
    (h2 : ∀ x ∈ I', MonoidAlgebra.domCongr ℂ ℂ e.symm x ∈ I) :
    killed (ρ.comp e.toMonoidHom : Representation ℂ H X) I = killed ρ I' := by
  ext v
  rw [mem_killed, mem_killed]
  constructor
  · intro h x hx
    have := h _ (h2 x hx)
    rw [asAlg_comp, ← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply] at this
    exact this
  · intro h x hx
    rw [asAlg_comp]
    exact h _ (h1 x hx)

theorem isDC_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (J : Subgroup H) (J' : Subgroup H')
    (hJ : ∀ g, g ∈ J ↔ e g ∈ J') (x : H) (R : Finset H) (h : Bridge.IsDC J x R) :
    Bridge.IsDC J' (e x) (R.map e.toEquiv.toEmbedding) := by
  have hJ' : ∀ g' : J', e.symm g' ∈ J := fun g' => (hJ _).2 (by simp)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨⟨e k₁, (hJ _).1 k₁.2⟩, ⟨e k₂, (hJ _).1 k₂.2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 (e.symm k₁ * x * e.symm k₂) ⟨⟨_, hJ' k₁⟩, ⟨_, hJ' k₂⟩, rfl⟩
    refine ⟨e a, ⟨Finset.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · have := (hJ _).1 ha'
      simpa using this
    · rintro b ⟨hb, hb'⟩
      obtain ⟨b, hbR, rfl⟩ := Finset.mem_map.1 hb
      have : b = a := hu b ⟨hbR, (hJ _).2 (by simpa using hb')⟩
      rw [this]; rfl

variable {D : D7}

theorem mem_levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GfC V) :
    (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      finE V (k : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ∧
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (k : GA D V)) : G0 Pg r) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem levChi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GA D V) :
    levChi V β (withP (princDat V.rank r t hr Pg χ) P) k =
      ((ext1 P.H P.chi (rTup β (princDat V.rank r t hr Pg χ) (finE V k) : G0 Pg r) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  congr 1
  have h1 : (withP (princDat V.rank r t hr Pg χ) P).s = 0 := rfl
  have h2 : (withP (princDat V.rank r t hr Pg χ) P).Q = ∅ := rfl
  rw [h1, h2]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem map_mem (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank)
    (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃* GfC V')
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (hrk : V.rank = V'.rank)
    (h1 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔
      finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ'))
    (h2 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) →
      (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) =
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r))
    (h3 : ∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α))
    (x : MonoidAlgebra ℂ (GfC V)) (hx : x ∈ eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) :
    MonoidAlgebra.domCongr ℂ ℂ Φ x ∈ eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg := by
  have hlev : ∀ (P : LevelP Pg r ℂ) (k : GfC V), (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      (Φ k : GA D V') ∈ levG V' β' (withP (princDat V'.rank r t hr' Pg χ') P) := by
    intro P k
    rw [mem_levG, mem_levG]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(h1 k).1 a, by rw [h2 k a]; exact b⟩
    · rintro ⟨a, b⟩
      have a' := (h1 k).2 a
      exact ⟨a', by rw [← h2 k a']; exact b⟩
  rcases hx with (⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩
  · refine Or.inl (Or.inl ⟨Φ k, (hlev P k).1 hk, ?_⟩)
    rw [levChi_eq, levChi_eq, h2 k ((mem_levG V β r t hr Pg χ P k).1 hk).1, map_sub, MonoidAlgebra.domCongr_single,
      MonoidAlgebra.domCongr_single, map_one Φ]
  · refine Or.inl (Or.inr ⟨fun g => Φ (κ g), fun g => ⟨(Φ (κ g)).2, (h1 _).1 (hκ g).2.1, ?_⟩, ?_⟩)
    · exact (h2 _ (hκ g).2.1).trans (hκ g).2.2
    · rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ]
      simp only [MonoidAlgebra.domCongr_single]
  · refine Or.inr ⟨P0, hP0, k, hrk ▸ hk, Φ α, R.map Φ.toEquiv.toEmbedding, (h3 P0 hP0 k α).1 hα, ?_, ?_⟩
    · rw [← map_inv Φ]
      exact isDC_map Φ _ _ (fun g => hlev (LevelP.triv Pg r ℂ) g) _ _ hR
    · rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ, Finset.sum_map]
      simp only [MonoidAlgebra.domCongr_single]
      rfl

theorem killed_eqSet_comp : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  intro D V V' β β' r t hr hr' Pg χ χ' Φ G _ _ eG c P Pl0 ok pl q Sg X _ _ ρ hrk h1 h2 h3
  refine killed_comp ρ Φ.toMulEquiv _ _
    (map_mem V V' β β' r t hr hr' Pg χ χ' Φ.toMulEquiv eG c P ok pl q Sg hrk h1 h2 h3) ?_
  have e : ∀ κ : GfC V', Φ (Φ.toMulEquiv.symm κ) = κ := fun κ => Φ.toMulEquiv.apply_symm_apply κ
  refine map_mem V' V β' β r t hr' hr Pg χ' χ Φ.toMulEquiv.symm eG c P ok pl q Sg hrk.symm ?_ ?_ ?_
  · intro κ
    rw [h1, e]
  · intro κ hκ
    have := h2 (Φ.toMulEquiv.symm κ) ((h1 _).2 (by rw [e]; exact hκ))
    rw [e] at this
    exact this.symm
  · intro P0 hP0 k α
    rw [h3 P0 hP0, e]

end GlobalTheory.CuspMult.EqTrans
