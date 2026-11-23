import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

private theorem cent_closed {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | x * g = g * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem UpperTheory.orbitalSideExtension_of_absoluteConvergence :
    SideAbs → RPF → RPE → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → Compat → GalCont → LocEmb → UnitIff → LocNorm → BoundE → N3 → N5 → P2 → SideE := by
  intro hSA hRPF hRPE hRPC hUL hUO hTC hSL hCL hCo hGC hLE hUI hLN hBE hN3 hN5 hP2 F E _ _ _ _ _ _ σ hσ n hn _ _ _ _ _ _ _ _ μ μi m hμ hμi hm γ hγ δ hδ ν νi nv hν hνi hnv S a b ha hb hET hEE
    φi φ hφi hφc hφ hS
  obtain ⟨c1, c2, c3, c4, -⟩ := hCo F E σ n
  obtain ⟨g0, g1, g2⟩ := hGC F E σ n
  obtain ⟨l1, l2⟩ := hLE F E n
  obtain ⟨t1, t2, t3, -⟩ := hTC F n γ hγ
  have hG := hRPE F E n
  have hT := hRPC _ _ _ _ (pI F n) (pF F n) (KF F n) (hRPF F n) (AdelicGLn.diagonal F n γ)
  haveI : LocallyCompactSpace (TA γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) :=
    fun v => (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TI γ : Subgroup _) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((TF γ v : Subgroup _) : Set (GL (Fin n) (v.adicCompletion F)))
  obtain ⟨uI, uV⟩ := hUL (Pl F) (GA E n) _ _ (pI E n) (fun v => pE E n v) (fun v => KE E n v) hG μ μi m hμ hμi hm
  have hZ : Continuous (zA E n) :=
    (continuous_centralSection (K := E) (n := n)).comp (Real.continuous_exp.subtype_mk _)
  have key := hSA (Pl F) (GA E n) (GL (Fin n) (InfiniteAdeleRing E)) (fun v => GL (Fin n) (CompletionsOver E v))
    (pI E n) (fun v => pE E n v) (fun v => KE E n v) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hG hT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ((mapGL n (infMap F E)).comp (TI γ).subtype)
    (fun v => (mapGL n (incFin E v)).comp (TF γ v).subtype)
    (fun t => c3 t.1) (fun v t => c4 v t.1) (fun v t => (hUI F E n v t.1).symm)
    μ μi m ν νi nv
    ⟨hμ, (hN5 F E σ hσ n hn).1.comp (cent_closed _).isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 t1⟩
    ⟨uI, (l1.comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ νi hνi).2 t2⟩
    (fun v => ⟨uV v, ((l2 v).comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ (nv v) (hnv v)).2 (t3 v)⟩)
    S a b ha hb hEE hET
    (mapGL n (galAd σ)) (mapGL n (galInf σ)) (fun v => mapGL n (galFin σ v)) c1 c2 g1 g2
    (AdelicGLn.diagonal E n δ) (zA E n) hZ
    (fun v s => (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v)
    (fun t => (hN3 F E σ hσ n hn δ γ hγ hδ _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, rfl⟩)
    (fun D hD => by
      obtain ⟨C, hC, hCx⟩ := (hP2 F E σ hσ n hn).2 (pI F n (AdelicGLn.diagonal F n γ)) (pI E n (AdelicGLn.diagonal E n δ))
        (hSL F n γ hγ).1 (hLN F E σ hσ n hn δ γ hδ).1 D hD
      refine ⟨C, hC, fun x hx => ?_⟩
      obtain ⟨t, ht, y, hy, rfl⟩ := hCx x hx
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩)
    (fun D hD => hBE F E σ hσ n hn (pI E n (AdelicGLn.diagonal E n δ)) D hD)
    φi φ hφi hφc hφ
    (fun v hv => by
      obtain ⟨e, hx⟩ := hS v hv
      refine ⟨e, fun x => ⟨fun h => ?_, ?_⟩⟩
      · obtain ⟨t, ht, y, hy, rfl⟩ := (hx x).1 h
        exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩
      · rintro ⟨t, y, hy, rfl⟩
        exact (hx _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, y, hy, rfl⟩)
  have hc : ∀ (s : ℝ) (x : GL (Fin n) (InfiniteAdeleRing E)),
      x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x =
        pI E n (zA E n s) * (x⁻¹ * pI E n (AdelicGLn.diagonal E n δ) * mapGL n (galInf σ) x) := by
    intro s x
    have h := (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1 x⁻¹
    rw [← mul_assoc x⁻¹, ← h]
    simp only [mul_assoc]
  refine ⟨key.1, ?_⟩
  simp only [hc]
  exact key.2
