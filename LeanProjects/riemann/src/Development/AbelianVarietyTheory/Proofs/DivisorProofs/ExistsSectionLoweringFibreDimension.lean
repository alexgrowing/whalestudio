import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem noetherianSpace_of_isArithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : NoetherianSpace X := by
  obtain ⟨N, j, hj, hjp⟩ := h.isProjOver
  haveI := h.isDomain
  haveI := h.finite
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  haveI : IsProper p := hjp ▸ inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  infer_instance

theorem exists_sec_fibre_dim_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z →
    (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) →
    ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  intro k _ X _ p D hX P hA d Z hZ hdim
  haveI : NoetherianSpace X := noetherianSpace_of_isArithVar hX
  have memfib : ∀ {x : X} {ℓ : ℕ}, x ∈ fib X ℓ ↔ ringChar (X.residueField x) = ℓ := Iff.rfl
  obtain ⟨hcov, hfibc, -, -, hWfib⟩ := GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX
  have hNV : ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) :=
    fun a b g hg => (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P a b g hg).1

  obtain ⟨e₀, g, hg, hfin0⟩ := GlobalTheory.T.exists_sections_cut_genericFibre_finite k X p D hX P hA d Z hZ (hdim 0)
  have hW₀c : IsClosed (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) :=
    hZ.sdiff (isOpen_iUnion fun j => hNV _ _ _ (hg j).2)

  have hpick0 : ∀ Y : irreducibleComponents ↥(Z ∩ fib X 0), ∃ y : ↥(Z ∩ fib X 0), y ∈ Y.1 ∧
      IsClosed ({y} : Set ↥(Z ∩ fib X 0)) := fun Y =>
    (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
  choose q₀ hq₀ hq₀c using hpick0
  haveI : Finite (irreducibleComponents ↥(Z ∩ fib X 0)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set W : Set X := (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) ∪ ⋃ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} with hWdef
  have hWc : IsClosed W := hW₀c.union (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hcl0 : ∀ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} ∩ fib X 0 ⊆ {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} := by
    rintro Y x ⟨hx, hx0⟩
    obtain ⟨K, hK, hKe⟩ := isClosed_induced_iff.1 (hq₀c Y)
    have hqK : ((q₀ Y : ↥(Z ∩ fib X 0)) : X) ∈ K := by
      have : q₀ Y ∈ Subtype.val ⁻¹' K := by rw [hKe]; rfl
      exact this
    have hxK : x ∈ K := closure_minimal (Set.singleton_subset_iff.2 hqK) hK hx
    have hxZ : x ∈ Z := closure_minimal (Set.singleton_subset_iff.2 (q₀ Y).2.1) hZ hx
    have : (⟨x, hxZ, hx0⟩ : ↥(Z ∩ fib X 0)) ∈ Subtype.val ⁻¹' K := hxK
    rw [hKe] at this
    exact congrArg Subtype.val this
  have hWfin : (W ∩ fib X 0).Finite := by
    refine (hfin0.union (Set.finite_range fun Y => ((q₀ Y : ↥(Z ∩ fib X 0)) : X))).subset ?_
    rintro x ⟨hx | hx, hx0⟩
    · exact Or.inl ⟨hx, hx0⟩
    · obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hx
      exact Or.inr ⟨Y, (hcl0 Y ⟨hY, hx0⟩).symm⟩

  obtain ⟨S, hSp, hWS⟩ := hWfib W hWc

  have hpick : ∀ i : (Σ ℓ : S, irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))), ∃ y : ↥(Z ∩ fib X (i.1 : ℕ)),
      y ∈ i.2.1 ∧ IsClosed ({(y : X)} : Set X) := by
    rintro ⟨ℓ, Y⟩
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ (hSp ℓ ℓ.2).ne_zero)
    obtain ⟨y, hy, hyc⟩ :=
      (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
    refine ⟨y, hy, ?_⟩
    have := hc.isClosedEmbedding_subtypeVal.isClosedMap _ hyc
    rwa [Set.image_singleton] at this
  choose q hq hqc using hpick
  haveI : ∀ ℓ : S, Finite (irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))) := fun _ =>
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hFc : IsClosed (Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X)) := by
    rw [← Set.iUnion_singleton_eq_range]
    exact isClosed_iUnion_of_finite hqc
  set T : Set X := closure (W ∩ fib X 0) ∪ Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X) with hTdef
  have hTc : IsClosed T := isClosed_closure.union hFc
  have hTfin : ∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite := fun ℓ =>
    ((GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre k X p D hX W hWc hWfin ℓ).union (Set.finite_range _)).subset fun x ⟨hx, hxl⟩ =>
      hx.elim (fun h => Or.inl ⟨h, hxl⟩) Or.inr

  obtain ⟨e, he, f, hf, hTNV⟩ := GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed k X p D hX P hA T hTc hTfin
  refine ⟨e, he, f, hf, fun ℓ => ?_⟩
  have hfo : IsOpen (NV P e 0 f) := hNV _ _ _ hf

  have key : ∀ Y ∈ irreducibleComponents ↥(Z ∩ fib X ℓ), (d : WithBot ℕ∞) ≤ topologicalKrullDim Y →
      ∃ s ∈ Y, (s : X) ∈ T := by
    intro Y hY hYd
    rcases eq_or_ne ℓ 0 with rfl | hℓ0
    · refine ⟨q₀ ⟨Y, hY⟩, hq₀ ⟨Y, hY⟩, Or.inl (subset_closure ⟨?_, (q₀ ⟨Y, hY⟩).2.2⟩)⟩
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨Y, hY⟩, subset_closure rfl⟩)
    by_cases hℓS : ℓ ∈ S
    · exact ⟨q ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, hq ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, Or.inr ⟨_, rfl⟩⟩
    obtain ⟨s₀, -⟩ := hY.1.nonempty
    have hℓp : ℓ.Prime := by
      rcases hcov (s₀ : X) with h | ⟨ℓ', hℓ', h⟩
      · exact absurd ((memfib.1 s₀.2.2).symm.trans (memfib.1 h)) hℓ0
      · rwa [(memfib.1 s₀.2.2).symm.trans (memfib.1 h)]
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ hℓ0)
    have hCi : IsIrreducible (Subtype.val '' Y) := hY.1.image _ continuous_subtype_val.continuousOn
    have hCc : IsClosed (Subtype.val '' Y) :=
      hc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents Y hY)
    have hCf : Subtype.val '' Y ⊆ fib X ℓ := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2.2
    have hCd : (d : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Subtype.val '' Y) := by
      rwa [← (Topology.IsEmbedding.subtypeVal.homeomorphImage Y).isHomeomorph.topologicalKrullDim_eq]
    obtain ⟨x, ⟨s, hsY, rfl⟩, hxg⟩ :=
      GlobalTheory.T.exists_common_zero_ample_sections_vertical k X p D hX P hA ℓ d (Subtype.val '' Y) e₀ g hℓp hCi hCc hCf hCd hg
    refine ⟨s, hsY, ?_⟩
    have hxW : (s : X) ∈ W := Or.inl ⟨s.2.1, hxg⟩
    rcases hWS hxW with h | h
    · exact Or.inl h
    · obtain ⟨ℓ', hℓ'S, h'⟩ := Set.mem_iUnion₂.1 h
      have : ℓ' = ℓ := (memfib.1 h').symm.trans (memfib.1 s.2.2)
      exact absurd (this ▸ hℓ'S) hℓS
  have hCsc : IsClosed {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} :=
    (hfo.preimage continuous_subtype_val).isClosed_compl
  have hdrop := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X ℓ)).1 _ d hCsc (hdim ℓ) fun Y hY hYd hsub => by
    obtain ⟨s, hsY, hsT⟩ := key Y hY hYd
    exact hsub hsY (hTNV hsT)
  have hset : Subtype.val '' {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} = (Z \ NV P e 0 f) ∩ fib X ℓ := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s.2.1, hs⟩, s.2.2⟩
    · rintro ⟨⟨hxZ, hxN⟩, hxl⟩
      exact ⟨⟨x, hxZ, hxl⟩, hxN, rfl⟩
  rw [← hset, ← (Topology.IsEmbedding.subtypeVal.homeomorphImage _).isHomeomorph.topologicalKrullDim_eq]
  exact hdrop

end GlobalTheory.HSAmp
