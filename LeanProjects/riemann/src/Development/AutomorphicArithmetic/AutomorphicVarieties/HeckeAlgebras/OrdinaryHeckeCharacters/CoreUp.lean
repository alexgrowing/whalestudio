import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.MemOrdC
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)

private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]

private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]

private theorem up_vec (hL : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.Part ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := ordA hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩

private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)

end

theorem UpperTheory.V.Hi.coreUp :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.Part ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
