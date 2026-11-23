import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Chi1LocIsGal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiTame
section General
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end General
theorem chi_one_tameGen_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  intro hP D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb hAu i k v hl
  obtain ⟨art, ha⟩ := hP D.host.E D.nd.Om
  have hj := X.nd.j_range i
  let j' : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  obtain ⟨n, hG⟩ := _root_.GlobalTheory.ChiLocGal.chi1_loc_isGal_alt D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb
    hAu art ha i j' (by simp only [j']; omega)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlp : (X.nd.l i).Prime := Fact.out
  have hgp := D.host.g_prime k
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  obtain ⟨hN, hg2, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ hgp (D.nd.g_split k) _ hwg
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
    GlobalTheory.GalChar.notMem_of_ne hgp hlp hl.symm hwg
  have hA := D.nd.plOm.2 (D.naut.plGw k v)
  obtain ⟨hp, -, hpg, -, hD⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec C' (l := X.nd.l i)
  have hdel : (cf.delAt (X.nd.l i)).UnrAt (D.naut.plGw k v) :=
    hD.unr _ (GlobalTheory.GalChar.notMem_of_ne hgp hp (hpg k).symm hwg)
  have hloc : ∀ x, IsUnitAt (D.naut.plGw k v) x →
      (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r).loc (D.naut.plGw k v) x =
        (cf.mu0 j').loc (D.naut.plGw k v) x := fun x hx => by
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hx, HChar.loc_mul, hdel x hx, mul_one]
  have hI := (hG.ine_pow_iff ha (Or.inl hwl) hA (D.host.g k - 1)).2 fun x hx => by
    rw [hloc x hx, ← hN]
    exact (GlobalTheory.Mem.WildChar.orders_on_units _ _ _).1 ((cf.isMu0 j').tame _) x hx
  haveI := D.host.isCMField_hostE
  obtain ⟨u, hu, hrep, hunit, σ, eσ, hσ⟩ := exists_tameRep hP ha hA hgp
    ((GlobalTheory.ChiLocGal.normV_eq_absNorm _).trans hN) hwg hg2 (fun a ha' x hx => isUnitAt_nat hwg ha' hx)
    (D.ntypes.tg_gen k v) _ (hG.cont (X.nd.O_adic i) (Sp.iq_alg i)) fun σ hσ => by
      rw [← map_pow, GlobalTheory.GalChar.inQ_eq_one, map_pow, hI σ hσ]
  obtain ⟨c, hc, hcv⟩ := A.chiT k v j' u hu hrep
  refine ⟨c, hc, ?_⟩
  have hvS : D.naut.plGw k v ∈ X.nd.S i := by
    rw [X.nd.S_def i]
    refine ⟨?_, hwl⟩
    fin_cases k
    · exact Or.inl hwg
    · exact Or.inr (Or.inl hwg)
  have hvQ : D.naut.plGw k v ∉ X.nd.Q i := fun h => (Finset.disjoint_left.mp (X.nd.SQ_disj i) hvS) h
  have hψ : T.psiL i (D.ntypes.tg k v) = 1 := by
    by_contra hne
    exact hvQ ((T.psiL_ram i _ _ hA).mp ⟨_, D.ntypes.tg_mem k v, hne⟩)
  have e1 := hG.loc (Or.inl hwl) eσ
  rw [GlobalTheory.GalChar.inQ_inj _ hσ, hloc _ hunit] at e1
  have e2 : X.nd.chi i 1 (D.ntypes.tg k v) = ((Units.map (T.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) (D.ntypes.tg k v) := by
    refine (DFunLike.congr_fun (T.chi_tw i) _).trans ?_
    exact (congrArg (_ * ·) hψ).trans (mul_one _)
  rw [← hcv, e2]
  refine Eq.trans ?_ e1
  unfold iotaO
  rw [hAu.iotaQ i]
  rfl
end GlobalTheory.ChiTame
end
end
