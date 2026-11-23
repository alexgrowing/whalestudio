import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ConjFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ShapeQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.MuPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.KillQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem muIne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ muOf l (Dec (F := F) A)) : s ∈ Ine (F := F) A := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨h1, a, h2⟩ := hs
  exact Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h2)

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem low_desc {A V : Type} [CommRing A] [CommRing V] [IsLocalRing V] (f : A →+* V) (hf : Function.Injective f)
    [IsLocalHom f] (ν : V) (hν : IsUnit ν) (X n₀ : M4 A) (hX : IsGSp ν (X.map f)) (h0 : IsLow (n₀.map f))
    (hs : SuppM nP ((X.map f).map (residue V))) (hd : ∀ i, IsUnit (((X.map f).map (residue V)) i i))
    (h0' : IsLow ((n₀.map f).map (residue V))) (hq : SuppM qQ ((n₀.map f).map (residue V))) :
    ∃ n : M4 A, IsLow n ∧ IsUp (adj n * X * n₀) := by
  have hG : ∀ (μ : A) (Y : M4 A), IsGSp (f μ) (Y.map f) → IsGSp μ Y := fun μ Y h => by
    unfold IsGSp at h ⊢
    rw [adj_map, ← Matrix.map_mul] at h
    ext i j
    apply hf
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hμ : f ((adj X * X) 0 0) = ν := by
    have h := hX
    unfold IsGSp at h
    rw [adj_map, ← Matrix.map_mul] at h
    simpa using congrFun (congrFun h 0) 0
  obtain ⟨⟨u1, u2⟩, -⟩ := Rq.shapeQ _ _ _ hs hd h0' hq
  rw [← Matrix.map_mul, ← Matrix.map_mul] at u1 u2
  simp only [Matrix.map_apply, ← map_mul, ← map_sub] at u1 u2
  refine Rq.luG A ((adj X * X) 0 0) X n₀ (IsUnit.of_map f _ (hμ ▸ hν)) (hG _ _ (hμ ▸ hX))
    ⟨hG 1 _ (by rw [map_one]; exact h0.1), fun i => hf ?_, fun i j hij => hf ?_⟩
    (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u1)) (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u2))
  · rw [map_one]; exact h0.2.1 i
  · rw [map_zero]; exact h0.2.2 i j hij

private theorem low_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n : M4 A} (h : IsLow n) : IsLow (n.map f) :=
  ⟨by simpa using isGSp_map f h.1, fun i => by rw [Matrix.map_apply, h.2.1, map_one],
    fun i j hij => by rw [Matrix.map_apply, h.2.2 i j hij, map_zero]⟩

private theorem up_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n X m : M4 A} (h : IsUp (adj n * X * m)) :
    IsUp (adj (n.map f) * X.map f * m.map f) := fun i j hij => by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, h i j hij, map_zero]

theorem UpperTheory.V.Ws.restrQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T₀ T : Tower D, T₀.Fit → T₀.Le T → ∀ (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V), QPair D T₀.pr (resQ T₀.F T₀.g0) 𝔞 P →
      LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) (P.map (residue 𝔞.V)) →
      ∃ P' : PD T.ι (G T.F Ω) 𝔞.V, 𝔞.Small P' ∧ (T.fr ∅).IsPair (𝔞.a c) P' ∧ P'.r = P.r.comp (resQ T.F) ∧
        T.OverQ (P.map (residue 𝔞.V)) (P'.map (residue 𝔞.V)) ∧ (T.fr ∅).IsRes (𝔞.red c) (P'.map (residue 𝔞.V)) ∧
        ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), P'.ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := by
  intro Ω _ _ _ l hl c D hD T₀ T hF hLe 𝔞 P hP hS
  have hOk : T.Ok := (leFit D hD T₀ T hLe).1 hF.1
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP.small
  haveI := hf.loc
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (𝔞.a c (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit ((((P₁.map f).map (residue 𝔞.V)).r x) i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  choose n hn hb using fun v : T.ι => low_desc f hf.inj _ (hν (g v)) (P₁.r (g v)) (P₁.n ()) (hP.pair.mult (g v))
    (hP.pair.low ()) (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag
  let Q : PD T.ι (G T.F Ω) A := ⟨P₁.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj ((Q.map f).n v) * (Q.map f).r s * (Q.map f).n v) ∧
      ∀ i, (Q.map f).ψ v i s = (P₁.map f).ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ ((P₁.map f).r (g v)) ((P₁.map f).r ((g v)⁻¹ * resQ T.F s * g v)) ((P₁.map f).r (resQ T.F s)) _ _
      (hν (g v)) (hP.pair.mult (g v)) (hP.pair.low ()) (low_map f (hn v)) (up_map f (hb v))
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.pair.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hI : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), (Q.map f).ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := fun v i s hs => by
    rw [(key v s (Ine_le_Dec _ hs)).2, hP.inert _ (hgI v s hs), hconj]
  have hpair : (T.fr ∅).IsPair (𝔞.a c) (Q.map f) := by
    refine ⟨fun x => hP.pair.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ (P₁.map f).r hP.pair.kill, ?_,
      fun v => low_map f (hn v), fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩
    · obtain ⟨j, hj⟩ := hLe.g0
      show ((P₁.map f).r (resQ T.F T.g0)).IsDiag
      have h := hP.pair.nrm
      change ((P₁.map f).r (resQ T₀.F T₀.g0)).IsDiag at h
      rw [hj, map_pow, ← h.diagonal_diag, Matrix.diagonal_pow]
      exact Matrix.isDiag_diagonal _
    · refine (hI v i s (muIne T.F l _ (T.ovl v) hs)).trans ?_
      rw [Rq.muPs D hD T hOk _ s hs i, Units.val_one, map_one]
  have hb' : ∀ v, IsUp (adj (((Q.map f).map (residue 𝔞.V)).n v) * ((P₁.map f).map (residue 𝔞.V)).r (g v) *
      ((P₁.map f).map (residue 𝔞.V)).n ()) := fun v => up_map (residue 𝔞.V) (up_map f (hb v))
  have hp' := hpair.map (residue 𝔞.V)
  refine ⟨Q.map f, ⟨A, _, _, inferInstance, f, Q, hf, fun i j N => (hc i j N).comp_continuous (cont_resQ T.F), rfl⟩, hpair, rfl,
    ⟨rfl, fun v => ⟨(), g v, hg v, hb' v⟩⟩, ⟨hp', ⟨fun x i => ?_, fun v s hs i => ?_, Or.inl ⟨fun x => hS.supp _, fun v => ?_⟩⟩,
      fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, hI⟩
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F x))
    rw [hLe.pr]
    exact hS.res.res.diag (resQ T.F x) i
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F s))
    refine (PD.map_ψ (Q.map f) (residue 𝔞.V) v i s).trans ?_
    rw [(key v s hs).2, ← PD.map_ψ, hLe.pr, ← hconj (chi D T₀.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  · exact (Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag).2 _ (hp'.low v) (hb' v)
