import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.neatLev_of :
    UpperTheory.Gal.Wt.NeatLev := by
  intro E _ _ _ l hl a ha w₀ hmem hs v' hv' hap K hK hint Kv hKv W f hf
  obtain ⟨N, hN, hNf⟩ := UpperTheory.Gal.Gen.smoothAt_holds E a w₀ hs W f
  obtain ⟨J, hJ, hJN, hJt, -⟩ := UpperTheory.Gal.Gen.tower_holds E w₀ a l hl hmem ha N hN
  obtain ⟨hLev, hmemC, hcJ, -, -, -⟩ :=
    UpperTheory.Gal.Gen.levFacts_holds E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hKC : K ≤ UpperTheory.Gal.Gen.lev K w₀ (J 0) := le_sup_left
  refine ⟨UpperTheory.Gal.Gen.lev K w₀ (J 0), hLev, hKC, ?_, ?_, ?_⟩
  · intro g γ hγ c hc x hx h
    have hT : UpperTheory.Gal.CharacterCongruences.TorsFreeAt (UpperTheory.Gal.Gen.lev K w₀ (J 0)) w₀ :=
      fun k hk ho => hJt _ (hcJ k hk) ho
    exact UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds E a _ ⟨hLev.fin, hLev.compact, hLev.isOpen⟩ w₀ hT
      g γ hγ c hc x hx h
  · have hKGL : GlobalTheory.LFun.KGL v' a ≤ (UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v') := by
      intro y hy
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a v' hv'
      have hy' : cLoc v' (e.symm y : UA E a) = y := by rw [← he]; simp
      exact ⟨(e.symm y : UA E a), hKC (hint _ (e.symm y).2 (hy'.symm ▸ hy)), hy'⟩
    have hmax := UpperTheory.Gal.Gen.maxCpt_holds E v' a ((UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v'))
      (cLoc v' '' (UpperTheory.Gal.Gen.lev K w₀ (J 0) : Set (UA E a)))
      (hLev.compact.image (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
      (fun _ h => h) hKGL
    intro c hc
    exact hmax ⟨c, hc, rfl⟩
  · intro c hc v g
    obtain ⟨hcC, hcv⟩ := hc
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (hmemC _).1 hcC
    have hx1 : cLoc v' x = 1 :=
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v') hap)
    have hkv : k ∈ K ⊓ Kv.comap (cLoc v') := by
      refine ⟨hk, ?_⟩
      have h2 : cLoc v' (k * x) ∈ Kv := hcv
      rw [map_mul, hx1, mul_one] at h2
      exact h2
    rw [← mul_assoc, hNf x hx (hJN hxJ) v (g * k)]
    exact hf k hkv v g
