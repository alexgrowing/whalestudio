import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactorStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC

theorem inv_fibQ (q N : ℕ) : Inv q (fibQ q N) := fun U ⟨x⟩ =>
  (show (invP q).obj (op U) from Sx.map (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N)) x).down

theorem inv_pullback_disc (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    Inv q (pullback (trivV N (disc.obj F)) (PGL.pr N)) := fun U ⟨x⟩ =>
  hF U ⟨Sx.map (pullback.fst (trivV N (disc.obj F)) (PGL.pr N)) x⟩

section
variable {q : ℕ}

theorem ev_comp_cochain {E : Spc} {I K : Cx (ZMod q)} {n d w : ℤ} (α : Cochain ((chains (ZMod q)).obj E) I n)
    (ψ : Cochain I K d) (h : n + d = w) (p : ℕ) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + w = t)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp ψ h) p t ht U x = Sec.map (ψ.v s t (by omega)) (ev α p s hs U x) := by
  rw [ev_def, ev_def, Cochain.comp_v α ψ h _ s t hs (by omega)]
  rfl

theorem cast_cocycle {E : Spc} {n n' i i' : ℤ} (hn : n' = n) (hi : i' = i)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i')) n') :
    ∃ γ' : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n,
      (CohomologyClass.mk γ' : Ht q E n i) = Ht.cast hn hi (CohomologyClass.mk γ) ∧
      ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (w : Sx E k V),
        ev γ'.1 k s hs V w = twCast hi (ev γ.1 k s (by omega) V w) := by
  subst hn hi
  exact ⟨γ, rfl, fun _ _ _ _ _ => rfl⟩

theorem sxmap_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

theorem coe_cocycle_sum {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle K L n) :
    ((∑ j ∈ t, c j : Cocycle K L n) : Cochain K L n) = ∑ j ∈ t, (c j : Cochain K L n) :=
  map_sum (AddMonoidHom.mk' (fun c : Cocycle K L n => (c : Cochain K L n)) (fun _ _ => rfl)) c t

theorem cochain_sum_v {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain K L n) (p p' : ℤ)
    (h : p + n = p') : (∑ j ∈ t, c j).v p p' h = ∑ j ∈ t, (c j).v p p' h :=
  map_sum (AddMonoidHom.mk' (fun c : Cochain K L n => c.v p p' h) (fun a b => Cochain.add_v a b p p' h)) c t

theorem Jsec_sum {N : ℕ} {I : Cx (ZMod q)} {n : ℤ} {U : Scheme.{0}} {ι : Type} (t : Finset ι)
    (c : ι → Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) I n) : Jsec (∑ j ∈ t, c j) = ∑ j ∈ t, Jsec (c j) :=
  map_sum ((toSheafify Scheme.etaleTopology.{0} (cotPre (ZMod q) q N I n)).app (op U)).hom c t

theorem ev_cocycle_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (↑(∑ j ∈ t, c j) : Cochain _ _ _) p s h U x = ∑ j ∈ t, ev (c j).1 p s h U x := by
  rw [coe_cocycle_sum]
  exact map_sum (evHom I n p s h U x) _ t

theorem ev_cochain_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (∑ j ∈ t, c j) p s h U x = ∑ j ∈ t, ev (c j) p s h U x :=
  map_sum (evHom I n p s h U x) c t

end

theorem pbf_disc_model : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  intro q _ N i
  have hz : ∀ j : Fin N, ∃ z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q ((j : ℕ) : ℤ)))
      (2 * ((j : ℕ) : ℤ)), CohomologyClass.mk z = cpow q (c1 q (lineQ q N)) (j : ℕ) :=
    fun j => (cpow q (c1 q (lineQ q N)) (j : ℕ)).mk_surjective
  choose z hz using hz
  have hψ := fun j : Fin N => GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing q N (i - (j : ℕ)) (j : ℕ) i (by ring) (j : ℕ) (z j)
  choose ψ hψ using hψ
  refine ⟨Jcx (ZMod q) q N (res (ZMod q) (tw q i)), ψ,
    GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE _ q N _ (inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)),
    GlobalTheory.T.injective_projBundleModelCochainComplex_X _ q N _ (fun m => inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X m))), ?_⟩
  intro F hF n
  obtain ⟨θ, hθ1, hθ2⟩ := GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre q N F hF
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre (ZMod q) q N (res (ZMod q) (tw q i)) F n
  let e₁ : Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i ≃+ Ht q (disc.obj F ⨯ fibQ q N) n i :=
    { toFun := pull _ θ.hom _ _
      invFun := pull _ θ.inv _ _
      left_inv := fun x => by rw [← pull_comp, θ.inv_hom_id, pull_id]
      right_inv := fun x => by rw [← pull_comp, θ.hom_inv_id, pull_id]
      map_add' := map_add _ }
  refine ⟨e₀.trans e₁.symm, fun a => ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  change e₀ _ = pull _ θ.hom _ _ (pbfMap q (trivV N (disc.obj F)) n i a)
  rw [GlobalTheory.T.pullback_projBundleFormulaMap_of_factor GlobalTheory.T.cup_chern_kummer_pullback_naturality q (trivV N (disc.obj F)) (lineQ q N) θ.hom prod.fst prod.snd (inv_fibQ q N)
    (inv_pullback_disc q N F hF) hθ1 hθ2 n i a]
  have hα := fun j : Fin N => GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos (ZMod q) F (res (ZMod q) (tw q (i - (j : ℕ)))) (n - 2 * ((j : ℕ) : ℤ)) (a j)
  choose α hαa hα0 using hα
  have hγ := fun j : Fin N => GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing q N F (α j) (z j) (hα0 j)
  choose γ hγc hγv using hγ
  have hγ' := fun j : Fin N => cast_cocycle (q := q) (E := disc.obj F ⨯ fibQ q N)
    (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) (show i - ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) = i by ring) (γ j)
  choose γ' hγ'c hγ'v using hγ'
  let mkH : ∀ {K L : Cx (ZMod q)} {m : ℤ}, Cocycle K L m →+ CohomologyClass K L m :=
    fun {K L m} => AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add
  have hL : (∑ j, cpost _ (ψ j) (n - 2 * ((j : ℕ) : ℤ)) n (by omega) (a j)) =
      CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) := by
    rw [show CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) =
      mkH (∑ j, zcomp (α j) (ψ j) _) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hαa j]
    rfl
  have hR : (∑ j : Fin N, ((cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (a j))
      (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (cpow q (c1 q (lineQ q N)) j))).cast (by ring) (by ring) :
        Ht q _ n i)) = CohomologyClass.mk (∑ j, γ' j) := by
    rw [show CohomologyClass.mk (∑ j, γ' j) = mkH (∑ j, γ' j) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = CohomologyClass.mk (γ' j)
    rw [hγ'c j, hγc j, hαa j, hz j]
  rw [hL, hR]
  apply he₀
  · intro p hp s h
    have key : ∀ j : Fin N, (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1.v
        (-(p : ℤ)) s h = 0 := fun j => by
      rw [show (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1 =
        (α j).1.comp (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) from rfl]
      rw [Cochain.comp_v _ _ _ _ (-(p : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) s rfl (by omega), hα0 j p hp _ rfl, zero_comp]
    rw [coe_cocycle_sum, cochain_sum_v]
    exact Finset.sum_eq_zero fun j _ => key j
  · intro U x
    have hc := fun j : Fin N => hψ j (n - 2 * ((j : ℕ) : ℤ)) n (by ring) U (ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x)
    choose c hc1 hc2 using hc
    refine ⟨∑ j, c j, ?_, ?_⟩
    · rw [ev_cocycle_sum, Jsec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc1 j]
      exact ev_comp_cochain (α j).1 (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) 0 _ n (by simp) (by simp) U x
    · intro k s hs V y
      rw [ev_cochain_sum, ev_cocycle_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc2 j, hγ'v j, hγv j]
      have e2 : Sx.map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y :=
        (sxmap_comp (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) prod.snd y).trans
          (by rw [prod.map_snd, Category.comp_id]; rfl)
      have e1 : (Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) : F.obj (op V)) =
          F.map (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U).op x :=
        (sxmap_comp (E := disc.obj (yoneda.obj U) ⨯ fibQ q N) _ _ y).trans (by
          rw [prod.map_fst]
          rfl)
      have e3 : Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U)
          (ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x) =
          ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k)
            (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) :=
        (ev_res _ _ _ _ _ _).trans (congrArg _ e1.symm)
      rw [e2, e3]

end GlobalTheory.EtC

end
