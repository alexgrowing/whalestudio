import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.SphLocProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit

noncomputable section

open NumberField IsDedekindDomain Filter Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

section Unram

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

theorem tendsto_finAdele (z : HeightOneSpectrum (𝓞 E) → Af E) (c : Af E)
    (hz : ∀ w u, pLoc E u (z w) ∈ u.adicCompletionIntegers E) (hc : ∀ u, pLoc E u c ∈ u.adicCompletionIntegers E)
    (he : ∀ u, ∀ᶠ w in cofinite, pLoc E u (z w) = pLoc E u c) : Tendsto z cofinite (𝓝 c) := by
  let A : ∀ u : HeightOneSpectrum (𝓞 E), Set (u.adicCompletion E) := fun u => u.adicCompletionIntegers E
  let g : HeightOneSpectrum (𝓞 E) → ∀ u, A u := fun w u => ⟨pLoc E u (z w), hz w u⟩
  let o : ∀ u, A u := fun u => ⟨pLoc E u c, hc u⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro u
    rw [tendsto_subtype_rng]
    exact tendsto_const_nhds.congr' ((he u).mono fun w hw => hw.symm)
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h2

theorem eventually_under_ne (u : HeightOneSpectrum (𝓞 E)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
  refine Filter.eventually_cofinite.2 ((Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} :
    Set (HeightOneSpectrum (𝓞 E)))).subset fun w hw => ?_)
  have hw' : ¬ u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := hw
  have hu : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := (not_not.1 hw').symm
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 hu with rfl | h
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 ?_)
    rw [eq_conjSrc h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]

theorem tendsto_val_locU (x : HeightOneSpectrum (𝓞 E) → UA E n) (hx : ∀ w, x w ∈ locU n w)
    (hK : ∀ w, cLoc w (x w) ∈ GlobalTheory.LFun.KGL w n) :
    Tendsto (fun w => (((x w : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E))) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : ∀ w, ((((x w : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 =
      ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := fun w => by
    have a := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j)
      (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 (hx w)).1)
    have b := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j)
      (map_one (cInf (E := E) (n := n)))
    exact (infEq E).symm.injective (a.trans b.symm)
  have h2 : Tendsto (fun w => ((((x w : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).2) cofinite
      (𝓝 ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).2) := by
    refine tendsto_finAdele _ _ (fun w u => GlobalTheory.UnramDict.cLoc_entry_mem (hx w) (hK w) u i j)
      (fun u => GlobalTheory.UnramDict.cLoc_entry_mem (one_mem (locU n u)) (by rw [map_one]; exact one_mem _) u i j)
      fun u => ?_
    filter_upwards [eventually_under_ne u] with w hw
    have a := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j)
      (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hx w)).2 u) hw))
    have b := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j)
      (map_one (cLoc (E := E) (n := n) u))
    exact a.trans b.symm
  exact ((tendsto_const_nhds (x := ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1)).congr
    fun w => (h1 w).symm).prodMk_nhds h2

theorem eventually_isUnramU {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsUnramU π w := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hπ.ne_bot
  have hS : {k : finU E n | RU E n k φ = φ} ∈ 𝓝 (1 : finU E n) :=
    (hπ.aut φ hφ).level.mem_nhds (by simp)
  have hy : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : UA E n, y ∈ locU n w ∧ cLoc w y ∈ GlobalTheory.LFun.KGL w n ∧
      (RU E n y φ = φ → ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ) := by
    intro w
    by_cases h : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ
    · exact ⟨1, one_mem _, by rw [map_one]; exact one_mem _, fun _ => h⟩
    · simp only [not_forall] at h
      obtain ⟨x, hx, hk, hne⟩ := h
      exact ⟨x, hx, hk, fun e => absurd e hne⟩
  choose y hyl hyK hyi using hy
  have hyf : ∀ w, y w ∈ finU E n := fun w => (Subgroup.mem_inf.1 (hyl w)).1
  have ht : Tendsto (fun w => (⟨y w, hyf w⟩ : finU E n)) cofinite (𝓝 1) := by
    rw [tendsto_subtype_rng, tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (tendsto_val_locU y hyl hyK).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (tendsto_val_locU (fun w => (y w)⁻¹) (fun w => inv_mem (hyl w)) fun w => by
        rw [map_inv]; exact inv_mem (hyK w)))
  filter_upwards [ht.eventually_mem hS] with w hw
  exact ⟨φ, hφ, h0, hyi w hw⟩

end Unram

section Main

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

theorem hasSatGL_of_isSubquotient {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hρs : IsSmooth ρ)
    (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (hsub : GlobalTheory.SmGL.IsSubquotient σ ρ)
    (hsph : GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w n)) (B : Multiset ℂˣ)
    (hsat : ∀ f ∈ fixed ρ (GlobalTheory.LFun.KGL w n), f ≠ 0 → GlobalTheory.LFun.IsSatVecGL w ρ f B) :
    GlobalTheory.LFun.HasSatGL w σ B := by
  obtain ⟨S, q, hq⟩ := hsub
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hSs : IsSmooth S.toRepresentation := fun y => by
    refine (congrArg IsOpen ?_).mpr (hρs y.1)
    ext g
    exact Subtype.ext_iff
  refine ⟨hsph, fun x hx hx0 => ?_⟩
  have hx' : x ∈ (fixed S.toRepresentation (GlobalTheory.LFun.KGL w n)).map q.toLinearMap := by
    rw [GlobalTheory.LocGL.map_fixed_of_surjective hSs hKc (f := q) hq]
    exact hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx'
  have hu0 : u ≠ 0 := fun e => hx0 (by rw [← hux, e, map_zero])
  have huK : u.1 ∈ fixed ρ (GlobalTheory.LFun.KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu k hk)
  have hu1 : GlobalTheory.LFun.IsSatVecGL w ρ u.1 B := hsat _ huK fun e => hu0 (Subtype.ext e)
  have hu2 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := ρ) S.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective hu1
  have hu3 : GlobalTheory.LFun.IsSatVecGL w σ (q.toLinearMap u) B :=
    hu2.map (ρ' := σ) q.toLinearMap (fun g y => Representation.IntertwiningMap.isIntertwining _ _ q g y)
      (by rw [hux]; exact hx0)
  rw [hux] at hu3
  exact hu3

theorem eventually_sat (X : Pre E n) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ S : Fin X.c → Multiset ℂˣ,
      (∀ i, GlobalTheory.LGrp.IsSpherical (X.σ i w).ρ (GlobalTheory.LFun.KGL w (X.N i)) ∧ GlobalTheory.LFun.HasSatGL w (X.σ i w).ρ (S i)) ∧
      ∀ f ∈ fixed (locProd X.h w (X.σ · w)) (GlobalTheory.LFun.KGL w n), f ≠ 0 →
        GlobalTheory.LFun.IsSatVecGL w (locProd X.h w (X.σ · w)) f (∑ i, S i) := by
  filter_upwards [Filter.eventually_all.2 fun i => GlobalTheory.SpehPair.eventually_spherical (X.discrete i)] with w hw
  have hsph : ∀ i, GlobalTheory.LGrp.IsSpherical (X.σ i w).ρ (GlobalTheory.LFun.KGL w (X.N i)) := fun i => hw i _ (X.loc i w)
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.Rigid.isSpherical_locProd X.h w (X.σ · w) hsph)
  obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.exists_sat_multiProd X.h (π := fun i => (X.σ i w).ρ) (fun i => (X.σ i w).smooth)
    (fun i => (X.σ i w).irred) hf hf0
  refine ⟨S, fun i => ⟨hsph i, hS i⟩, fun f' hf' hf'0 => ?_⟩
  obtain ⟨S', hS', hfS'⟩ := GlobalTheory.SatInd.exists_sat_multiProd X.h (π := fun i => (X.σ i w).ρ)
    (fun i => (X.σ i w).smooth) (fun i => (X.σ i w).irred) hf' hf'0
  have e : S' = S := funext fun a => (hS' a).unique (hS a)
  rw [← e]
  exact hfS'

theorem splitSatPre : SplitSatPre := by
  intro E _ _ _ n π hπ D D' hD hD'
  filter_upwards [eventually_sat D, eventually_sat D', eventually_isUnramU hπ, hD.compl_mem_cofinite,
    hD'.compl_mem_cofinite] with w h1 h2 hu hw hw' hs
  obtain ⟨S, hS, hSf⟩ := h1
  obtain ⟨S', hS', hS'f⟩ := h2
  have hw2 : ¬ (IsSplitAt w ∧ ¬ D.SplitAt π w) := hw
  have hw2' : ¬ (IsSplitAt w ∧ ¬ D'.SplitAt π w) := hw'
  obtain ⟨P, hPsub, hPc⟩ : D.SplitAt π w := not_not.1 fun h => hw2 ⟨hs, h⟩
  obtain ⟨P', hP'sub, hP'c⟩ : D'.SplitAt π w := not_not.1 fun h => hw2' ⟨hs, h⟩
  have hP := hasSatGL_of_isSubquotient (locProd D.h w (D.σ · w)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P.ρ hPsub
    (GlobalTheory.PfBCI.split_spherical hπ hs P hPc hu) _ hSf
  have hP' := hasSatGL_of_isSubquotient (locProd D'.h w (D'.σ · w)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P'.ρ hP'sub
    (GlobalTheory.PfBCI.split_spherical hπ hs P' hP'c hu) _ hS'f
  have h3 := GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ w hs _ _ P.ρ P'.ρ hPc hP'c _ hP
  exact ⟨∑ i, S i, ⟨S, hS, rfl⟩, ⟨S', hS', (h3.unique hP').symm⟩⟩

end Main

end PositivityTheory.Rg.BcB.F.Rig

end
