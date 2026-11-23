import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DefIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBstab
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBdim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCfix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTsurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GgMapOfGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMazur

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), L.Pres := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  haveI : CharP (ResidueField O) l := IsCoef.char
  haveI : IsNoetherianRing L.O' := inferInstance
  haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete
  haveI : Finite (ResidueField L.O') := IsCoef.fin
  haveI : CharP (ResidueField L.O') l := IsCoef.char
  have hU : NRep.Univ L.O' L.ρ := by
    refine ⟨(loc_rho hF hn S x L).1, ?_⟩
    intro C _ _ _ ρ' hc hb
    exact def_iso hF hn S x L C ρ' hc hb
  obtain ⟨B, hBo, hBc⟩ := pr_box hF L.R (maximalIdeal L.R) L.ρ (loc_rho hF hn S x L).1 (fun v => flag hF hn S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨φ, hφ⟩ := (pr_res hF hn S x L).1
  have hG := pr_good hF hn (ResidueField L.O') φ _ hφ
  haveI : Module.Finite (ResidueField L.O') (Tan L.O' L.R) := (pr_tan L.O' L.R).1
  have hBo' := hBo.map (res L.O' L.R : L.R →+* ResidueField L.O')
  have hres := pr_res hF hn S x L
  have hcount := pr_count (K := ResidueField L.O') F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b
    ((Box.tanCo L.O' B).comp (Tan L.O' L.R).subtype)
    (fun v Y hY => pr_brig (ResidueField L.O') _ (Box.bar L.O' B) hBo' hG.1 v Y hY)
    (fun z hz => by
      obtain ⟨D, hD, X, hX⟩ := pr_tsurj hF L.O' L.R L.ρ B hU hBo hBc hG.1 z hz
      exact ⟨⟨D, hD⟩, X, hX⟩)
  obtain ⟨D₀, hD₀, hD₀s⟩ := pr_tor hF L.O' L.R L.ρ B hU hBo hBc hG.1 hG.2.2
  have h1 := hcount.2 _ ⟨D₀, hD₀⟩ hG.2.1 hD₀s
  have hec := hF.ec (ResidueField L.O') (Matrix (Fin n) (Fin n) (ResidueField L.O')) (Box.bar L.O' B).ad (Box.bar L.O' B).b
    (pr_open hF L.O' L.R B hBc).2.1
    (fun v s X hX => pr_bstab _ (Box.bar L.O' B) v s X hX)
    (fun f hf => pr_dual hF hn (ResidueField L.O') φ _ (Box.bar L.O' B) hBo' hφ hres.2 f hf)
  have h2K : (2 : ResidueField L.O') ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).1 (by exact_mod_cast h)
    have hl := (Fact.out : l.Prime)
    have h4 := Nat.le_of_dvd (by norm_num) hd
    have h5 := hl.two_le
    have h6 := hF.l_odd
    omega
  have hκ : ∀ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = (n * n - n) / 2 := by
    intro w
    have hsq : (Box.bar L.O' B).r (F.cw w) * (Box.bar L.O' B).r (F.cw w) = 1 := by
      rw [← map_mul, hF.cw_sq w, map_one]
    have hr : ((Box.bar L.O' B).r (F.cw w)).right = -1 := by
      rw [(Box.bar L.O' B).nu, hF.del_cw w]
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker + n = n * n :=
      pr_cfix (ResidueField L.O') n _ h2K hsq hr
    have hle : n ≤ n * n := Nat.le_mul_self n
    omega
  have hβ : ∀ v : F.V, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = (n * n - n) / 2 + n := by
    intro v
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = n * (n + 1) :=
      pr_bdim (ResidueField L.O') n ((Box.bar L.O' B).g v)
    have hle : n ≤ n * n := Nat.le_mul_self n
    have e : n * (n + 1) = n * n + n := by ring
    omega
  have hsum1 : ∑ v : F.V, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = F.d * ((n * n - n) / 2) + F.d * n := by
    rw [Finset.sum_congr rfl (fun v _ => by rw [hβ v]), ← Finset.sum_mul]
    show F.d * ((n * n - n) / 2 + n) = _
    ring
  have hsum2 : ∑ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = F.d * ((n * n - n) / 2) := by
    simp only [hκ, Finset.sum_const, Finset.card_univ, smul_eq_mul, hF.card_inf]
  have hT : Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) + n * F.d + 1 ≤ Module.finrank (ResidueField L.O') (Tan L.O' L.R) := by
    have e := hec.2
    rw [hsum1, hsum2] at e
    have : n * F.d = F.d * n := Nat.mul_comm _ _
    omega
  have hobs : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := by
    intro C' _ _ _ p hp hm
    obtain ⟨D⟩ := pr_setlift hF L.O' C' L.R p B hp hm hBc
    have hZ : ∀ u, D.co u ∈ continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b := by
      intro u
      obtain ⟨_, _, hlc1, hlc2⟩ := pr_omk hF L.O' C' L.R p B D hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hlc1.comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro v
        exact (hlc2 v).comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro s t r
        exact borelProjection_isTwoCocycle hF L.O' C' L.R p B D u hm s t r
      · intro v s t
        exact pr_cocv hF L.O' C' L.R p B D u hm v s t
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ D.co hZ), ?_⟩
    intro u hu C'' _ _ _ q p'' hc hq hk
    refine pr_obs hF L.O' L.R L.ρ B hU hBo hBc hG.1 C' p D u hm ?_ C'' q p'' hc hq hk
    have h' : (⟨D.co u, hZ u⟩ : continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) ∈
        Submodule.comap (continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b).subtype (continuousCoboundaries2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) :=
      (Submodule.Quotient.mk_eq_zero _).1 hu
    exact h'
  haveI : Module.Finite (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := hec.1
  have hobs' : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b ×
      (Fin (Module.finrank (ResidueField L.O') (Tan L.O' L.R) - (n * F.d + 1) -
        Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)) → ResidueField L.O')) := by
    intro C' _ _ _ p hp hm
    obtain ⟨ob, hob⟩ := hobs C' p hp hm
    refine ⟨(LinearMap.inl _ _ _).comp ob, fun u hu => hob u ?_⟩
    simpa using hu
  obtain ⟨p, f, hs, hk⟩ := pr_mazur L.O' L.R _ hobs'
  refine ⟨_, _, p, f, ?_, hs, hk⟩
  rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega
