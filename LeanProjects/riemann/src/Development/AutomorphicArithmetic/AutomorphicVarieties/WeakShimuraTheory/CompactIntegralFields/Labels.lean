import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ExNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Choice
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.PairOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ParEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.StarConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ent_of_map {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) {r : Γ →* M4 R} {w : ℤ × ℤ}
    (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, hw, hne⟩ := h
  refine ⟨g, i, j, hw, fun h0 => hne ?_⟩
  have e : mapRep f r g i j = f (r g i j) := rfl
  rw [e, h0, map_zero]

private theorem mapRep_eq {Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (r : Γ →* M4 R) (g : Γ) :
    mapRep f r g = (r g).map f := rfl

theorem UpperTheory.V.Ws.labels :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → ∃ pr, LabOk D pr ∧ ∀ g0 : G ℚ Ω,
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) →
      ∃ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P ∧ NearSplit D pr 𝔞 P ∧ IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r) ∧
        (Star (mapRep 𝔞.toK r) → StarE P.r) := by
  intro Ω _ _ _ l _ c D hD 𝔞 r u hK
  obtain ⟨pr, hok, hunit⟩ := Lab.choice D hD 𝔞 r u hK
  refine ⟨pr, hok, fun g0 hsep => ?_⟩
  have hwinv : ∀ Y : M4 𝔞.V, wM 𝔞.V pr * (adj (wM 𝔞.V pr) * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, sp_mul_adj (wM_sp pr), Matrix.one_mul]
  obtain ⟨hs, hsep2⟩ := sg_sep hD 𝔞 pr
  have hcg := hK.cg pr
  have hconj : adj (adj (wM 𝔞.V pr) * u) * (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr) *
      (adj (wM 𝔞.V pr) * u) = adj u * r (D.sg l) * u := by
    rw [adj_mul, adj_adj]
    simp only [Matrix.mul_assoc, hwinv]
  obtain ⟨-, -, -, himp⟩ := Lab.resFlag 𝔞.V (adj (wM 𝔞.V pr) * r (D.sg l) * wM 𝔞.V pr)
    (adj (wM 𝔞.V pr) * u) (fun i => 𝔞.a c ((chi D pr i (D.sg l) : (c.O)ˣ) : c.O))
    (fun i => 𝔞.a c ((D.ps i (D.sg l) : (c.O)ˣ) : c.O)) (hcg _) (sp_mul (sp_adj (wM_sp pr)) hK.sp)
    (by rw [hconj]; exact hK.flag _ hs) (by rw [hconj]; exact hK.char _ hs) hsep2
  have hminor := (himp hunit).1
  have hoff : ∀ i j, i ≠ j → (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i j ∈ maximalIdeal 𝔞.V := by
    intro i j hij
    have h := hcg g0 i j
    rwa [Matrix.diagonal_apply_ne _ hij, sub_zero] at h
  have hdiff : ∀ i j, i ≠ j → IsUnit ((adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) i i -
      (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) j j) := by
    intro i j hij
    apply unit_of_sub_mem (𝔞.unit_sub (hsep i j hij))
    have h1 := hcg g0 i i
    have h2 := hcg g0 j j
    simp only [Matrix.diagonal_apply_eq] at h1 h2
    have h3 := (maximalIdeal 𝔞.V).sub_mem h1 h2
    rw [sub_sub_sub_comm] at h3
    exact h3
  obtain ⟨P, v, b, hsm, hv, hv1, hPr, hdg, hlow, hb, hbup, hfac⟩ := Lab.exNorm 𝔞 (G ℚ Ω) r u pr g0
    (𝔞.a c ((D.th g0 : (c.O)ˣ) : c.O)) hK.small (𝔞.unit_two c hD.l_odd) ((D.th g0).isUnit.map _)
    (hK.mult g0) hK.sp _ _ rfl rfl hoff hdiff hunit hminor
  obtain ⟨hQ, hN⟩ := Lab.pairOf D hD 𝔞 r u hK pr g0 P v b hok hsm hv hv1 hPr hdg hlow hb hbup hfac
  have hm : IsGSp 1 (wM 𝔞.V pr * v) := sp_mul (wM_sp pr) hv
  have hinj : Function.Injective 𝔞.toK := fun x y h => Subtype.ext h
  have hmap : ∀ g, mapRep 𝔞.toK P.r g =
      adj ((wM 𝔞.V pr * v).map 𝔞.toK) * mapRep 𝔞.toK r g * (wM 𝔞.V pr * v).map 𝔞.toK := by
    intro g
    rw [mapRep_eq, mapRep_eq, hPr g, adj_map, Matrix.map_mul, Matrix.map_mul]
  have hparM : (∀ g, Par (mapRep 𝔞.toK r g)) → Par ((wM 𝔞.V pr * v).map 𝔞.toK) := by
    intro hp
    have hpr : Par (r g0) := fun i j hij => hinj (by
      have h := hp g0 i j hij
      rw [mapRep_eq, Matrix.map_apply] at h
      rw [h, map_zero])
    have hX : Par (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) :=
      Par.mul (Par.mul (Par.adj (wM_par pr)) hpr) (wM_par pr)
    have hXv : (adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr) * v = v * Matrix.diagonal (P.r g0).diag := by
      rw [hdg.diagonal_diag, hPr g0, adj_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc v (adj v), sp_mul_adj hv, Matrix.one_mul]
    have hpv : Par v := Lab.parEig 𝔞.V _ v _ hoff hdiff hv1 hXv hX
    have hpm := Par.mul (wM_par pr) hpv
    intro i j hij
    rw [Matrix.map_apply, hpm i j hij, map_zero]
  refine ⟨P, hQ, hN, ?_, ?_⟩
  · refine ⟨⟨(adj (wM 𝔞.V pr * v)).map 𝔞.toK, (wM 𝔞.V pr * v).map 𝔞.toK, ?_, ?_⟩, fun g => ?_⟩
    · rw [← Matrix.map_mul, sp_adj_mul hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [← Matrix.map_mul, sp_mul_adj hm, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hmap g, adj_map]
      rfl
  · intro hstar
    have hgm : IsGSp 1 ((wM 𝔞.V pr * v).map 𝔞.toK) := by
      simpa using gsp_map 𝔞.toK hm
    obtain ⟨h1, h2, h3⟩ := Lab.starConj 𝔞.K (G ℚ Ω) (mapRep 𝔞.toK r) (mapRep 𝔞.toK P.r)
      ((wM 𝔞.V pr * v).map 𝔞.toK) hgm hmap hparM hstar
    refine ⟨ent_of_map _ h1, ent_of_map _ h2, ?_⟩
    rcases h3 with h | h | h
    · exact Or.inl (ent_of_map _ h)
    · exact Or.inr (Or.inl (ent_of_map _ h))
    · exact Or.inr (Or.inr (ent_of_map _ h))
