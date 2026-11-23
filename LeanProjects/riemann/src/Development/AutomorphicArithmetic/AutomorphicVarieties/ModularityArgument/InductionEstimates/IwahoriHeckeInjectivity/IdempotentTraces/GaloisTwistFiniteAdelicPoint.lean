import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.T2SpaceGlCompletionsOver
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.MatchOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem central_fixed (σ : E ≃ₐ[F] E) (s : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n s) = centralSection E n s := by
  have hd : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
  have hroot : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^
      Module.finrank F E = s := by
    apply Subtype.ext
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  rw [← hroot, ← UpperTheory.centralSection_baseChange F E n]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

private theorem galois_twist_finite_adelic_point (σ : E ≃ₐ[F] E) (hn : 0 < n) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}
    (hθ : IsGalTwist σ θ) {x x' : FA E n} (h : mapGL n (galAd σ) (finEmb E n x) = finEmb E n x') :
    θ.e (fin1 x) = fin1 x' := by
  change θ.e (retractOne (finEmb E n x)) = retractOne (finEmb E n x')
  have h1 : ((θ.e (retractOne (finEmb E n x)) : G1 E n) : AdelicGLn.AdelicGL E n) *
      centralSection E n (detModule E n (finEmb E n x)) = finEmb E n x' := by
    rw [hθ, coe_retractOne, map_mul, map_inv, central_fixed, inv_mul_cancel_right, h]
  rw [← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]

private theorem indicator_prod {v : Pl F} (UE : Subgroup (GL (Fin n) (CompletionsOver E v)))
    (H : ∀ u : PlacesOver E v, Set (Gw n u.1)) (h : ∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ H u) :
    (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 = GM.prodFn fun u => (H u).indicator 1 := by
  funext g
  rw [GM.prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ UE
  · rw [Set.indicator_of_mem (show g ∈ (UE : Set _) from hg)]
    exact (Finset.prod_eq_one fun u _ => Set.indicator_of_mem ((h g).1 hg u) _).symm
  · rw [Set.indicator_of_notMem (show g ∉ (UE : Set _) from hg)]
    obtain ⟨u, hu⟩ := not_forall.1 fun hh => hg ((h g).2 hh)
    exact (Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem hu _)).symm

private theorem iwCoset_zero_eq (w : Pl E) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w)) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

private theorem indicator_test {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G) (h : CO J) :
    Test ((J : Set G).indicator (1 : G → ℂ)) ∧
      ∀ u ∈ J, ∀ g, (J : Set G).indicator (1 : G → ℂ) (u * g) = (J : Set G).indicator 1 g ∧
        (J : Set G).indicator (1 : G → ℂ) (g * u) = (J : Set G).indicator 1 g := by
  have hcl : IsClopen (J : Set G) := ⟨Subgroup.isClosed_of_isOpen J h.2, h.2⟩
  refine ⟨⟨?_, HasCompactSupport.intro h.1 fun x hx => Set.indicator_of_notMem hx _⟩, fun u hu g => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ (J : Set G)
    · exact ⟨J, h.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨(J : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · have h1 : u * g ∈ (J : Set G) ↔ g ∈ (J : Set G) := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ (J : Set G) ↔ g ∈ (J : Set G) := Subgroup.mul_mem_cancel_right J hu
    simp only [Set.indicator_apply, h1, h2, Pi.one_apply, and_self]

private theorem split_level (v : Pl F) (hv : GM.Split E v) (u₀ : PlacesOver E v)
    (U₀ : ∀ u : PlacesOver E v, Subgroup (Gw n u.1))
    (hU : ∀ u, CO (U₀ u) ∧ U₀ u ≤ GLnLocal.integralGL (u.1.adicCompletion E) n) :
    ∃ (A : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)), CO A ∧
      A ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
      ∀ u, CO (J u) ∧ J u ≤ U₀ u ∧ ∀ g, g ∈ A ↔ mapGL n (completionMap v u.1) g ∈ J u := by
  have hL := fun u : PlacesOver E v => UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n
  choose e he using fun u => (hL u).1
  let A : Subgroup (Gw n v) := ⨅ u, (U₀ u).comap (mapGL n (completionMap v u.1))
  have hA : ∀ g, g ∈ A ↔ ∀ u, e u g ∈ U₀ u := fun g => by
    simp only [A, Subgroup.mem_iInf, Subgroup.mem_comap, he]
  have hAo : IsOpen (A : Set (Gw n v)) := by
    have hset : (A : Set (Gw n v)) = ⋂ u, (e u) ⁻¹' (U₀ u : Set (Gw n u.1)) := by
      ext g
      simp only [SetLike.mem_coe, hA, Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact isOpen_iInter_of_finite fun u => (hU u).1.2.preimage (e u).continuous
  have hAc : IsCompact (A : Set (Gw n v)) := by
    have hc : IsCompact ((e u₀) ⁻¹' (U₀ u₀ : Set (Gw n u₀.1))) :=
      (e u₀).toHomeomorph.isCompact_preimage.2 (hU u₀).1.1
    exact hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen A hAo) fun g hg => (hA g).1 hg u₀
  have hJ : ∀ u, ((A.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = e u '' A := fun u => by
    rw [Subgroup.coe_map]
    exact Set.image_congr fun g _ => (he u g).symm
  refine ⟨A, fun u => A.map (mapGL n (completionMap v u.1)), ⟨hAc, hAo⟩, fun g hg => ?_, fun u => ⟨⟨?_, ?_⟩, ?_, fun g => ⟨?_, ?_⟩⟩⟩
  · exact ((hL u₀).2.1 g).1 ((hU u₀).2 (by rw [← he]; exact (hA g).1 hg u₀))
  · rw [hJ]; exact hAc.image (e u).continuous
  · rw [hJ]; exact (e u).toHomeomorph.isOpenMap _ hAo
  · rintro _ ⟨g, hg, rfl⟩
    rw [← he]; exact (hA g).1 hg u
  · exact fun hg => ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', h⟩
    rw [← he, ← he] at h
    rwa [← (e u).injective h]

end SlopeTestRemainingChoices

section Key

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private structure LevelAt (σ : E ≃ₐ[F] E) (q : Pl F) (S : Finset (Pl F)) (U₀ : ∀ w : Pl E, Subgroup (Gw n w)) (v : Pl F)
    (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : ℂ) (f : Gw n v → ℂ)
    (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)) : Prop where
  co : (∀ u, CO (J u) ∧ J u ≤ GLnLocal.integralGL (u.1.adicCompletion E) n)
  mem : (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u)
  stable : (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u)
  off : (v ∉ S → v ≠ q → (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧
        f = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 ∧
        UF = GLnLocal.integralGL (v.adicCompletion F) n ∧ ∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n)
  at_q : (v = q → f = (GM.iwCoset v 0).indicator 1 ∧ UF = GLnLocal.iwahori (v.adicCompletion F) n ∧
        ∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n)
  in_S : (v ∈ S → (∀ u, J u ≤ U₀ u.1) ∧
        IsLocallyConstant ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ)) ∧
        HasCompactSupport ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ)) ∧
        IsLocallyConstant f ∧ HasCompactSupport f ∧
        IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
        IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        (∀ y ∈ UE, ∀ g, (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (y * g) =
          (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) g) ∧
        (∀ y ∈ UF, ∀ g, f (y * g) = f g) ∧
        GM.MatchAt σ v c ((UE : Set (GL (Fin n) (CompletionsOver E v))).indicator 1) f)

end Key

section Key

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
  [IsTotallyComplex E] {n : ℕ}

private theorem level_at (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (hp : (Module.finrank F E).Prime) (hn : 0 < n)
    (q : Pl F) (S : Finset (Pl F)) (hqS : q ∉ S) (hsp : ∀ v ∈ S, GM.Split E v) (U₀ : ∀ w : Pl E, Subgroup (Gw n w)) (hU₀ : Lev U₀)
    (v : Pl F) :
    ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : ℂ) (f : Gw n v → ℂ)
      (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)), LevelAt σ q S U₀ v J c f UE UF := by
  have hne : Nonempty (PlacesOver E v) := by
    obtain ⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩
  obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := UpperTheory.ConvolutionTheory.T.offStable F E σ hσ hp n hn v
  by_cases hvS : v ∈ S
  · obtain ⟨u₀⟩ := hne
    have hv := hsp v hvS
    obtain ⟨A, J, hA, hAi, hJ⟩ := split_level v hv u₀ (fun u => U₀ u.1) fun u => hU₀ u.1
    obtain ⟨s1, s2⟩ := UpperTheory.ConvolutionTheory.T.splitStable F E σ hσ hp n hn v hv A J fun u => (hJ u).2.2
    obtain ⟨UE, e1, e2, e3⟩ := s2 hA hAi
    obtain ⟨c, hc⟩ := UpperTheory.ConvolutionTheory.T.splitMatch F E σ hσ hp n hn v u₀ hv A J hA fun u => ⟨(hJ u).1, (hJ u).2.2⟩
    have hi := indicator_test (J u₀) (hJ u₀).1
    obtain ⟨m1, m2, m3, m4, m5⟩ := hc _ hi.1 hi.2
    have hφ : Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) u₀
        ((J u₀ : Set (Gw n u₀.1)).indicator 1) = fun u => (J u : Set (Gw n u.1)).indicator 1 :=
      Function.update_eq_self u₀ _
    rw [hφ, ← indicator_prod UE (fun u => (J u : Set (Gw n u.1))) e1] at m1 m2 m4
    exact ⟨J, c, _, UE, A, ⟨fun u => ⟨(hJ u).1, (hJ u).2.1.trans (hU₀ u.1).2⟩, e1, s1, fun h => absurd hvS h,
      fun h => absurd (h ▸ hvS) hqS, fun _ => ⟨fun u => (hJ u).2.1, m2.1, m2.2, m3.1, m3.2, e2, e3, hA.2, hAi,
        fun y hy => m4 y ((e1 y).1 hy), m5, m1⟩⟩⟩
  · by_cases hvq : v = q
    · exact ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, 0, (GM.iwCoset v 0).indicator 1, U2,
        GLnLocal.iwahori (v.adicCompletion F) n, ⟨fun u => ⟨(o5 u.1).2.1, (o5 u.1).2.2⟩, o4, o2,
        fun _ h => absurd hvq h, fun _ => ⟨rfl, rfl, fun _ => rfl⟩, fun h => absurd h hvS⟩⟩
    · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, 0,
        (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1, U1, GLnLocal.integralGL (v.adicCompletion F) n,
        ⟨fun u => ⟨(o5 u.1).1, le_rfl⟩, fun g => ?_, o1, fun _ _ => ⟨o3, rfl, rfl, fun _ => rfl⟩,
        fun h => absurd h hvq, fun h => absurd h hvS⟩⟩
      rw [← SetLike.mem_coe, o3]
      exact Iff.rfl

end Key

section Build

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem exists_loc (σ : E ≃ₐ[F] E) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (hqS : q ∉ S)
    (hunr : ∀ v ∉ S, GM.Unr E v) (U₀ : ∀ w : Pl E, Subgroup (Gw n w))
    (J : ∀ v : Pl F, ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (c : Pl F → ℂ) (f : ∀ v : Pl F, Gw n v → ℂ)
    (UE : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : ∀ v : Pl F, Subgroup (Gw n v))
    (k : ∀ v, LevelAt σ q S U₀ v (J v) (c v) (f v) (UE v) (UF v)) :
    ∃ L : GM.Loc σ n q w₀, L.S = S ∧ L.UE = UE ∧ ∀ v, L.φ v = (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 := by
  have hq : ∀ g, g ∈ UE q ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n := fun g =>
    ((k q).mem g).trans (forall_congr' fun u => by rw [((k q).at_q rfl).2.2 u])
  have hφq : (UE q : Set (GL (Fin n) (CompletionsOver E q))).indicator (1 : GL (Fin n) (CompletionsOver E q) → ℂ) = GM.iwFn w₀ 0 := by
    refine (indicator_prod (UE q) (fun u => (GLnLocal.iwahori (u.1.adicCompletion E) n : Set _)) hq).trans ?_
    unfold GM.iwFn
    congr 1
    funext u
    rw [ite_self, iwCoset_zero_eq]
  refine ⟨⟨S, hqS, hunr, fun v => (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1, f, c, UE, UF, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, fun _ => rfl⟩
  · exact fun v hv => by
      obtain ⟨-, a, b, d, e, -⟩ := (k v).in_S hv
      exact ⟨a, b, d, e⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, a, b, d, e, -⟩ := (k v).in_S hv
      exact ⟨a, b, d, e⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, -, -, -, -, a, b, -⟩ := (k v).in_S hv
      exact ⟨a, b⟩
  · exact fun v hv => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, a⟩ := (k v).in_S hv
      exact a
  · exact ⟨hφq, ((k q).at_q rfl).1, hq, ((k q).at_q rfl).2.1⟩
  · intro v a b
    obtain ⟨e1, e2, e3, -⟩ := (k v).off a b
    refine ⟨?_, e2, e1, e3⟩
    change (UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 = _
    rw [e1]

end Build

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem mem_levOn_iff (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n) (x : FA E n) :
    x ∈ levOn SE U ↔ ∀ w, finAt w (finEmb E n x) ∈ U w := by
  have hite : ∀ w, (if w ∈ SE then U w else GLnLocal.integralGL (w.adicCompletion E) n) = U w := fun w => by
    split_ifs with hw
    · rfl
    · exact (hU w hw).symm
  exact forall_congr' fun w => by rw [← hite w]

private theorem cmp_atFin (v : Pl F) (u : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp u (mapGL n (atFin v) g) = finAt u.1 g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem levE_eq (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n)
    (UE : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (hm : ∀ (v : Pl F) g, g ∈ UE v ↔ ∀ u : PlacesOver E v, GM.cmp u g ∈ U u.1) :
    GM.levE UE = levOn SE U := by
  ext x
  rw [mem_levOn_iff SE U hU]
  simp only [GM.levE, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply]
  constructor
  · intro h w
    have := (hm _ _).1 (h (w.under (𝓞 F))) ⟨w, ⟨rfl⟩⟩
    rwa [cmp_atFin] at this
  · intro h v
    refine (hm v _).2 fun u => ?_
    rw [cmp_atFin]
    exact h u.1

private theorem twist_stable (σ : E ≃ₐ[F] E) (hn : 0 < n) (SE : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw n w))
    (hU : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n)
    (hs : ∀ (v : Pl F) (x : GL (Fin n) (CompletionsOver E v)), (∀ u : PlacesOver E v, GM.cmp u x ∈ U u.1) →
      ∀ u : PlacesOver E v, GM.cmp u (mapGL n (galFin σ v) x) ∈ U u.1)
    {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ) (x : FA E n) (hx : x ∈ levOn SE U) :
    ∃ x' ∈ levOn SE U, θ.e (fin1 x) = fin1 x' := by
  obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  have hI : finEmb E n (AdelicGLn.prodEquiv E n (mapGL n (galAd σ) (finEmb E n x))).2 =
      mapGL n (galAd σ) (finEmb E n x) := by
    apply (AdelicGLn.prodEquiv E n).injective
    rw [prodEquiv_finEmb]
    refine Prod.ext ?_ rfl
    have e1 : ∀ g : AdelicGLn.AdelicGL E n, (AdelicGLn.prodEquiv E n g).1 = T4.pI E n g := fun g =>
      Units.ext (Matrix.ext fun a b => AdelicGLn.prodEquiv_apply_fst E n g a b)
    have e2 : T4.pI E n (finEmb E n x) = 1 := by rw [← e1, prodEquiv_finEmb]
    change 1 = _
    rw [e1, c1, e2, map_one]
  refine ⟨_, ?_, galois_twist_finite_adelic_point σ hn hθ hI.symm⟩
  rw [mem_levOn_iff SE U hU, hI]
  intro w
  have h1 := (mem_levOn_iff SE U hU x).1 hx
  have h3 : mapGL n (atFin (w.under (𝓞 F))) (mapGL n (galAd σ) (finEmb E n x)) =
      mapGL n (galFin σ (w.under (𝓞 F))) (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) := c2 _ _
  have h4 := hs _ (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) (fun u => by
    rw [cmp_atFin]; exact h1 u.1) ⟨w, ⟨rfl⟩⟩
  rwa [← h3, cmp_atFin] at h4

end Lev

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.locSm :
    LocSm := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ n hn q w₀ S hqS hunr hsp U₀ hU₀ SE hSE
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  choose J c f UE UF k using level_at (n := n) σ hσ hp hn q S hqS hsp U₀ hU₀
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  let U : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), U u.1 = J v u := by
    rintro v ⟨w, hw⟩
    obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩
    rfl
  have hoff : ∀ w, w ∉ SE → U w = GLnLocal.integralGL (w.adicCompletion E) n := fun w hw => by
    have hw' := mt (hSE w).2 hw
    rw [not_or] at hw'
    exact ((k _).off hw'.1 hw'.2).2.2.2 ⟨w, ⟨rfl⟩⟩
  have hm : ∀ (v : Pl F) g, g ∈ UE v ↔ ∀ u : PlacesOver E v, GM.cmp u g ∈ U u.1 := fun v g =>
    ((k v).mem g).trans (forall_congr' fun u => by rw [eJ])
  have hs : ∀ (v : Pl F) (x : GL (Fin n) (CompletionsOver E v)), (∀ u : PlacesOver E v, GM.cmp u x ∈ U u.1) →
      ∀ u : PlacesOver E v, GM.cmp u (mapGL n (galFin σ v) x) ∈ U u.1 := fun v x hx u => by
    rw [eJ]
    exact (k v).stable x (fun u => by rw [← eJ]; exact hx u) u
  obtain ⟨L, hS, hUE, hφ⟩ := exists_loc σ q w₀ S hqS hunr U₀ J c f UE UF k
  refine ⟨L, U, hS, fun w => (k _).co ⟨w, ⟨rfl⟩⟩, fun w hw => ((k _).in_S hw).1 ⟨w, ⟨rfl⟩⟩,
    fun w hw => ((k _).at_q hw).2.2 ⟨w, ⟨rfl⟩⟩, ?_, fun v => ?_, fun μ _ θ hθ x hx => twist_stable σ hn SE U hoff hs hθ x hx⟩
  · rw [hUE]
    exact levE_eq SE U hoff UE hm
  · rw [hφ, hUE]
