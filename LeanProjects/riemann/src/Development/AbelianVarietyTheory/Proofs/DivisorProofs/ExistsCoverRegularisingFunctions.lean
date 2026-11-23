import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupEffectiveCartierCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMorphismGenericPointSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.Principal

section Alg

variable {K K' : Type} [Field K] [Field K'] {R : Subring K} {R' : Subring K'} {σ τ : Type} [Fintype σ] [Fintype τ]

theorem lc_map (φ : K →+* K') (hφ : ∀ a ∈ R, φ a ∈ R') {g : σ → K} {a : K} (h : Lc R g a) :
    Lc R' (fun s => φ (g s)) (φ a) := by
  obtain ⟨α, hα, rfl⟩ := h
  exact ⟨fun s => φ (α s), fun s => hφ _ (hα s), by simp only [map_sum, map_mul]⟩

theorem gen_of_lc {f : σ → K} {g : τ → K} {η : K} (h : Gen R g η) (hf : ∀ s, Lc R g (f s))
    (hg : ∀ t, Lc R f (g t)) : Gen R f η := by
  obtain ⟨h0, h1, β, hβ, hη⟩ := h
  refine ⟨h0, fun s => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := hf s
    rw [e, Finset.sum_div]
    exact sum_mem fun t _ => by rw [mul_div_assoc]; exact R.mul_mem (hα t) (h1 t)
  · choose γ hγ e using hg
    refine ⟨fun s => ∑ t, β t * γ t s, fun s => sum_mem fun t _ => R.mul_mem (hβ t) (hγ t s), ?_⟩
    rw [hη]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [e t, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring

end Alg

section Sch

theorem fnMap_fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens} (e : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (s : Γ(X, U)) :
    SmallSec.fnMap j hη (fnOf U h s) = fnOf V h' ((j.appLE U V e).hom s) := by
  rw [SmallSec.fnMap_fnOf j hη h (e h'), ← fnOf_resG e h']
  rfl

variable {X : Scheme.{0}} [IsIntegral X]

theorem ov_iff {p : ℕ} {x : X} : Ov p x ↔ x ∉ X.basicOpen (p : Γ(X, ⊤)) := by
  rw [Scheme.mem_basicOpen X (U := ⊤) _ x (show x ∈ (⊤ : X.Opens) from trivial), map_natCast]
  rfl

theorem exists_affine_nbhd {p : ℕ} {κ σ : Type} [Fintype κ] [Fintype σ] (f : X → κ → σ → X.functionField) (x : X)
    (h1 : ∀ i s, RegAt x (f x i s))
    (h2 : ∀ i, ∃ (s : σ) (a : ℕ), f x i s ≠ 0 ∧ RegAt x ((p : X.functionField) ^ a / f x i s))
    (h3 : ∀ᶠ z in 𝓝 x, Ov p z → ∀ i s, Lc (loc z) (f x i) (f z i s) ∧ Lc (loc z) (f z i) (f x i s)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ (∀ z ∈ U, ∀ i s, RegAt z (f x i s)) ∧
      (∀ i, ∃ (s : σ) (a : ℕ), f x i s ≠ 0 ∧ ∀ z ∈ U, RegAt z ((p : X.functionField) ^ a / f x i s)) ∧
      ∀ z ∈ U, Ov p z → ∀ i s, Lc (loc z) (f x i) (f z i s) ∧ Lc (loc z) (f z i) (f x i s) := by
  choose s a hs ha using h2
  have e1 : ∀ᶠ z in 𝓝 x, ∀ i s, RegAt z (f x i s) :=
    eventually_all.2 fun i => eventually_all.2 fun s => eventually_regAt (h1 i s)
  have e2 : ∀ᶠ z in 𝓝 x, ∀ i, RegAt z ((p : X.functionField) ^ a i / f x i (s i)) :=
    eventually_all.2 fun i => eventually_regAt (ha i)
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 (e1.and (e2.and h3))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxO hOo
  exact ⟨U, hU, hxU, fun z hz => (hO (hUO hz)).1,
    fun i => ⟨s i, a i, hs i, fun z hz => (hO (hUO hz)).2.1 i⟩, fun z hz => (hO (hUO hz)).2.2⟩

end Sch

end GlobalTheory.LatChain.Principal

namespace GlobalTheory.LatChain

open GlobalTheory.LatChain.Principal

theorem exists_cover_gen_of_lc : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime →
    ∀ (κ σ : Type) [Fintype κ] [Fintype σ] (f : V.X → κ → σ → V.X.functionField), (∀ x, Ov p x →
      (∀ i s, RegAt x (f x i s)) ∧ (∀ i, ∃ (s : σ) (a : ℕ), f x i s ≠ 0 ∧ RegAt x ((p : V.X.functionField) ^ a / f x i s)) ∧
      ∀ᶠ z in 𝓝 x, Ov p z → ∀ i s, Lc (loc z) (f x i) (f z i s) ∧ Lc (loc z) (f z i) (f x i s)) →
    ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), π ≫ V.p = V'.p ∧ Lies V' V π ∧
      ∀ x, Ov p x → ∀ i, ∃ η, Gen (loc x) (fun s => SmallSec.fnMap π hπ (f (π x) i s)) η := by
  intro F _ _ Y V p hp κ σ _ _ f H
  haveI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
  haveI : IsNoetherian V.X := V.ar.isNoetherian
  have hloc : ∀ x : {x : V.X // Ov p x}, ∃ U : V.X.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧
      (∀ z ∈ U, ∀ i s, RegAt z (f x.1 i s)) ∧
      (∀ i, ∃ (s : σ) (a : ℕ), f x.1 i s ≠ 0 ∧ ∀ z ∈ U, RegAt z ((p : V.X.functionField) ^ a / f x.1 i s)) ∧
      ∀ z ∈ U, Ov p z → ∀ i s, Lc (loc z) (f x.1 i) (f z i s) ∧ Lc (loc z) (f z i) (f x.1 i s) :=
    fun x => exists_affine_nbhd f x.1 (H x.1 x.2).1 (H x.1 x.2).2.1 (H x.1 x.2).2.2
  choose U hUa hxU hreg hpa hLc using hloc
  have hC : IsCompact {x : V.X | Ov p x} := by
    have e : {x : V.X | Ov p x} = (V.X.basicOpen (p : Γ(V.X, ⊤)) : Set V.X)ᶜ := Set.ext fun x => ov_iff
    rw [e]
    exact (V.X.basicOpen _).isOpen.isClosed_compl.isCompact
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x => (U x : Set V.X)) (fun x => (U x).isOpen)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxU _⟩
  have hsec : ∀ (l : {x : V.X // Ov p x}) (i : κ) (s : σ),
      ∃ c : Γ(V.X, U l), fnOf (U l) (gen_mem (hxU l)) c = f l.1 i s :=
    fun l i s => exists_fnOf_eq _ fun z hz => hreg l z hz i s
  choose c hc using hsec
  let e := Fintype.equivFin (↥t × κ)
  let eσ := Fintype.equivFin σ
  have hrad : ∀ (l : {x : V.X // Ov p x}) (i : κ), (p : Γ(V.X, U l)) ∈
      (Ideal.span (Set.range fun k : Fin (Fintype.card σ) => c l i (eσ.symm k))).radical := by
    intro l i
    obtain ⟨s, a, hs0, hpa'⟩ := hpa l i
    obtain ⟨b, hb⟩ := exists_fnOf_eq (gen_mem (hxU l)) hpa'
    refine ⟨a, ?_⟩
    have h1 : (p : Γ(V.X, U l)) ^ a = b * c l i s := fnOf_injective _ (gen_mem (hxU l)) (by
      rw [map_mul, hb, hc, map_pow, map_natCast, div_mul_cancel₀ _ hs0])
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨eσ s, by simp⟩)
  obtain ⟨J, hJs, hJ⟩ := GlobalTheory.Principalise.exists_idealSheaf_principalises V.X p _
    (fun j => U (e.symm j).1.1) (fun _ => Fintype.card σ) (fun j k => c (e.symm j).1.1 (e.symm j).2 (eσ.symm k))
    (fun j => hUa _) (fun j => hrad _ _)
  obtain ⟨V', Z, b, ν, hE, hcomp, hLies⟩ := GlobalTheory.T.exists_blowup_effective_cartier_cover F Y V p hp.ne_zero J hJs
  have hπ := GlobalTheory.T.cover_morphism_generic_point_specializes F Y V V' (ν ≫ b) hLies
  refine ⟨V', ν ≫ b, hπ, hcomp, hLies, fun x' hx' i => ?_⟩
  have hz : Ov p ((ν ≫ b) x') := hx'.map (ν ≫ b)
  obtain ⟨l, hlt, hzl⟩ : ∃ l ∈ t, (ν ≫ b) x' ∈ U l := by simpa using ht hz
  obtain ⟨j, hj⟩ : ∃ j, e.symm j = (⟨l, hlt⟩, i) := ⟨e _, e.symm_apply_apply _⟩
  have hmem : (ν ≫ b) x' ∈ U (e.symm j).1.1 := by rw [hj]; exact hzl
  have hi : (e.symm j).2 = i := by rw [hj]
  obtain ⟨W0, hW, hxW, -, k, hdiv⟩ := hJ Z V'.X b ν hE x' j hmem
  have hgW : genericPoint V'.X ∈ W0 := gen_mem hxW
  have hval : ∀ s, SmallSec.fnMap (ν ≫ b) hπ (f (e.symm j).1.1.1 (e.symm j).2 s) =
      fnOf W0 hgW (((ν ≫ b).appLE _ W0 hW).hom (c (e.symm j).1.1 (e.symm j).2 s)) := fun s => by
    rw [← hc, fnMap_fnOf_appLE _ hπ hW (gen_mem (hxU _)) hgW]
  have hd : ∀ s, ((ν ≫ b).appLE _ W0 hW).hom (c (e.symm j).1.1 (e.symm j).2 (eσ.symm k)) ∣
      ((ν ≫ b).appLE _ W0 hW).hom (c (e.symm j).1.1 (e.symm j).2 s) := fun s => by
    have := hdiv (eσ s)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  choose d hd using hd
  obtain ⟨η, hη⟩ : ∃ η, η = fnOf W0 hgW (((ν ≫ b).appLE _ W0 hW).hom (c (e.symm j).1.1 (e.symm j).2 (eσ.symm k))) :=
    ⟨_, rfl⟩
  have hfac : ∀ s, SmallSec.fnMap (ν ≫ b) hπ (f (e.symm j).1.1.1 (e.symm j).2 s) = η * fnOf W0 hgW (d s) := fun s => by
    rw [hval, hd, map_mul, hη]
  obtain ⟨s0, a0, hs0, -⟩ := hpa (e.symm j).1.1 (e.symm j).2
  have hne : η ≠ 0 := fun h0 => hs0 ((SmallSec.fnMap (ν ≫ b) hπ).injective (by rw [hfac, h0, zero_mul, map_zero]))
  have hgen : Gen (loc x') (fun s => SmallSec.fnMap (ν ≫ b) hπ (f (e.symm j).1.1.1 (e.symm j).2 s)) η := by
    refine ⟨hne, fun s => ?_, fun s => if s = eσ.symm k then 1 else 0, fun s => ?_, ?_⟩
    · dsimp only
      rw [hfac, mul_div_cancel_left₀ _ hne]
      exact mem_loc.2 (regAt_fnOf hxW hgW _)
    · dsimp only
      split_ifs
      exacts [one_mem _, zero_mem _]
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hval, hη]
  have hφ := map_mem_loc (ν ≫ b) hπ x'
  have hgen' : Gen (loc x') (fun s => SmallSec.fnMap (ν ≫ b) hπ (f ((ν ≫ b) x') (e.symm j).2 s)) η :=
    gen_of_lc hgen
      (fun s => lc_map _ hφ (hLc (e.symm j).1.1 _ hmem hz (e.symm j).2 s).1)
      (fun s => lc_map _ hφ (hLc (e.symm j).1.1 _ hmem hz (e.symm j).2 s).2)
  rw [hi] at hgen'
  exact ⟨η, hgen'⟩

end GlobalTheory.LatChain
