import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch

open scoped CategoryTheory.Obj in

theorem isAb_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' := by
  have hB := Out.TLinPf.isAb_pullback f A hA
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback A f)
  have hc := hB.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine { comm := ⟨?_⟩, smooth := ?_, proper := ?_, geomConnected := ?_ }
  · rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]
  · exact MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth
  · exact MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper
  · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected

theorem sym_of_cancel {S S' X : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {M : LB X} {F : A.left ⟶ X} {Φ : A'.left ⟶ X}
    (e : φ ≫ F = Φ) (hM : M.IsLB) {L : LB A.left} (hL : L.IsLB) {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hs : Out.Sym A L) : Out.Sym A' (M.pull Φ) := by
  subst e
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  obtain ⟨c, hc, -⟩ := exists_up hw hM hL t ht
  refine gen_chartPull (chartPullLinComb M (φ ≫ F) _ _ _ (φ.resLE _ _ le') fun k => ?_) c hc
  have hψ' : ∀ q : A.left ⟶ X, φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι ≫ q = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ ≫ q := fun q => by
    rw [← Category.assoc, hψ, Category.assoc]
  fin_cases k
  · show (_ ≫ _) ≫ φ ≫ F = _ ≫ (_ ≫ _) ≫ F
    simp only [Category.assoc]
    rw [hψ', ← Category.assoc _ φ F, GlobalTheory.PolBaseChange.inv_comm h, Category.assoc]
  · show (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ ≫ F = φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι ≫ F
    rw [hψ']

theorem exists_pgen_cancel {X X₁ X₂ : Scheme.{0}} {M : LB X} {L : LB X₁} {F : X₁ ⟶ X} {ψ : X₂ ⟶ X₁} {Φ : X₂ ⟶ X}
    (e : ψ ≫ F = Φ) (hM : M.IsLB) (hL : L.IsLB) (w : LB.Iso L (M.pull F)) (hw : PGen w) :
    ∃ w' : LB.Iso (M.pull Φ) (L.pull ψ), PGen w' := by
  subst e
  have h₂ := pull_isLB hM (ψ ≫ F)
  have g := (isGen_iff _).1 (idIso_isGen h₂)
  obtain ⟨w', T⟩ := exists_cancel hM w (idIso _) hw g hL h₂
  exact ⟨w', T.pgen_cancel hM hw g⟩

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n m : ℕ} (h : n = m)
    (v : Fin m → (epsR R ⟶ G)) (hv : IsLieBasis fun i : Fin n => v (i.cast h)) : IsLieBasis v := by
  subst h
  exact hv

theorem valF_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (dualMap (f'.comp f)) = spMap (Chart.dualMapR f') ≫ spMap (dualMap f) := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, dualMap]

theorem keyPB_of_keyOver {R R' R'' : Type} [CommRing R] [Field R'] [Field R''] (f : R →+* R') (f' : R' →+* R'')
    (t : SAB H (Sp R)) (th : t.PP.L.Sec) (x' : KeyIn R') (x'' : KeyIn R'') (v' : Fin x'.P.g → (epsR R ⟶ t.G))
    (v'' : Fin x''.P.g → (epsR R ⟶ t.G)) (hg : x''.P.g = x'.P.g) (hvv : ∀ i, v'' i = v' (i.cast hg))
    (h' : KeyOver f t th x' v') (h'' : KeyOver (f'.comp f) t th x'' v'') : KeyPB x'' x' f' := by
  obtain ⟨φ, he, w, hc, hw, hr, hs, hv⟩ := h'
  obtain ⟨φ'', he'', w'', hc'', hw'', hr'', hs'', hv''⟩ := h''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec t.G) _ x'.rig t.PP.rig (spMap f) _ (rigPull_le φ (spMap f) he t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec t.G) _ x''.rig t.PP.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  refine ⟨φ', he', w', hg, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (φ (φ' (q z)))
    have a := (KeyCancel.appLE_eq_iff_stalk w th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w'' th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, Category.assoc, hv, hv'', hvv, spMap_dualMap_comp, Category.assoc]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem valAt'_appLE {X Y : Scheme.{0}} (r : Sp ℂ ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ F ⁻¹ᵁ U)
    (hr : ⊤ ≤ r ⁻¹ᵁ V) (f : Γ(X, U)) : valAt' r V ((F.appLE U V e).hom f) = valAt' (r ≫ F) U f := by
  have h₂ : ⊤ ≤ (r ≫ F) ⁻¹ᵁ U := fun p hp => e (hr hp)
  rw [TB.ValAt.valAt'_of _ _ hr, TB.ValAt.valAt'_of _ _ h₂]
  simp only [valAt]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem norm_key_of_frame : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : KeyIn L) (th : D.t.PP.L.Sec) (s : Out.H0 D.t.PP.L 1) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)) (e : Fin D.g → D.B.carrier), KeyDeg.SameSec s th → KeyOver (algebraMap (𝓞 L) L) D.t th x v → IsLieBasis v → (∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left) → ∀ (σ : L →+* ℂ) (a : D.Frame σ) (θ : (Fin D.g → ℂ) → ℂ) (W : Matrix (Fin D.g) (Fin D.g) ℂ) (Fd : Set (Fin D.g → ℂ)), a.IsFn s θ → (∀ i, D.IsVec a (e i) (W i)) → IsAddFundamentalDomain a.u.Λ Fd volume → ‖σ (κ L x : L)‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4 * ((volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * D.g) := by
  intro κ hF hA E _ _ _ H L _ _ D x th s hg v e hss hov hb hve σ a θ W Fd hθ hW hFd
  obtain ⟨φ₁, he₁, w₁, hc₁, hw₁, hr₁, hs₁, hv₁⟩ := id hov
  have hsp : emb σ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc₁.1
  obtain ⟨ψ, hψ, hψ0⟩ : ∃ ψ : a.A.left ⟶ x.P.A.left, ψ ≫ φ₁ = a.φ ∧ ψ ≫ x.P.A.hom = a.A.hom ≫ spMap σ :=
    ⟨hp.lift a.φ (a.A.hom ≫ spMap σ) (by rw [Category.assoc]; exact a.cart.1.w.trans (congrArg (a.A.hom ≫ ·) hsp)), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  have hc : IsGrpPullback a.A x.P.A (spMap σ) ψ := hc₁.cancel (a.cart.congr hsp hψ.symm) hψ0
  have hM := D.t.PP.isLB
  have hL₂ := pull_isLB hM a.φ
  have g₁ := (isGen_iff w₁).1 hw₁
  obtain ⟨w', gw'⟩ := exists_pgen_cancel hψ hM x.P.isLB w₁ g₁
  have hab := isAb_of_isGrpPullback hc x.P.isAb
  haveI : IsCommMonObj a.A := hab.comm
  have hsm : SmoothOfRelativeDimension D.g a.A.hom := by
    have h₀ := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hc.1 x.P.smoothDim
    rwa [hg] at h₀
  have he₂ : eSec a.A ≫ a.φ = emb σ ≫ eSec D.t.G := GlobalTheory.PolBaseChange.eSec_comm a.cart
  let r₂ := rigPullOf a.φ (emb σ) he₂ D.t.PP.L D.t.PP.rig
  have hr₂ : r₂.IsGen := Out.LBxP.isGen_pullAlong D.t.PP.L a.φ (emb σ) (fun _ : PUnit => eSec D.t.G) (fun _ => 1)
    (fun _ => eSec a.A) (fun _ => he₂) D.t.PP.rig D.t.PP.rigGen
  have hsym := sym_of_cancel hc hψ hM x.P.isLB g₁ x.P.sym
  have hamp := relAmple_pull hc.1 x.P.isLB hL₂ gw' ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
  have hk := kTriv_pull hc x.P.isLB hL₂ gw' x.P.ktriv
  let P' : Out.PolAV (Sp ℂ) :=
    { A := a.A, isAb := hab, g := D.g, smoothDim := hsm, L := D.t.PP.L.pull a.φ, isLB := hL₂, rigid := ⟨r₂, hr₂⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  have gid := (isGen_iff _).1 (idIso_isGen hL₂)
  obtain ⟨th', hth'⟩ := sec_pull_down (L := D.t.PP.L) (F := a.φ) (w := idIso _) gid hM hL₂ th
  have hthe : ∀ (j : D.t.PP.L.ι) (y : a.A.left), a.φ y ∈ D.t.PP.L.U j →
      gs a.φ y _ (th.f j) = gs (𝟙 _) y _ (th'.f fun _ => j) := fun j y hj => by
    have h := hth' _ (𝟙 _) y j (fun _ => j) hj (mem_pull.2 hj)
    rw [Category.id_comp] at h
    refine h.trans ?_
    have : gw (idIso (D.t.PP.L.pull a.φ)) (𝟙 _) y j (fun _ => j) = 1 := gm_self hL₂ (𝟙 _) y (mem_pull.2 hj)
    rw [this, Units.val_one, _root_.one_mul]
  have hne : ∀ p : Sp ℂ, ∃ y : P'.A.left, P'.A.hom y = p ∧ y ∈ Out.nonzeroLocus th' := by
    intro p
    obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap σ p)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hc.1 z p hz
    obtain ⟨k, hk', u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨j, hj⟩ := exists_chart hM (a.φ y)
    have hj' : φ₁ (ψ y) ∈ D.t.PP.L.U j := by
      rw [← hψ] at hj
      exact hj
    have a₁ := (KeyCancel.appLE_eq_iff_stalk w₁ th x.th).1 hs₁ _ ψ y j k hj' hk'
    have u₁ : IsUnit (gs ψ y _ (x.th.f k)) := by rw [gs_stalkMap ψ y _ hk']; exact u.map _
    have u₂ : IsUnit (gs a.φ y _ (th.f j)) := by rw [← hψ, a₁]; exact (Units.isUnit _).mul u₁
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => j, mem_pull.2 hj, ?_⟩⟩
    rw [← hthe j y hj]
    exact u₂
  have hvv : ∀ i : Fin D.g, ∃ v' : epsR ℂ ⟶ a.A,
      v'.left ≫ a.φ = spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt (e i)).left ∧ a.u.IsDiff (W i) v' := by
    intro i
    obtain ⟨v₀, hl, v', h1, h2⟩ := hW i
    refine ⟨v', h1.trans ?_, h2⟩
    rw [LieModel.Lifts, Category.comp_id] at hl
    exact hl
  choose v' hv'1 hv'2 using hvv
  have hv' : ∀ j : Fin x.P.g, (v' (j.cast hg)).left ≫ ψ = spMap (Chart.dualMapR σ) ≫ (x.v j).left := by
    intro j
    apply hp.hom_ext
    · rw [Category.assoc, hψ, hv'1, Category.assoc, hv₁, hve j, spMap_dualMap_comp, Category.assoc]
    · rw [Category.assoc, hψ0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have := x.P.isAb.smooth
  have hbasis : IsLieBasis v' := isLieBasis_cast hg v' (Chart.isLieBasis_baseChange σ hc x.basis hv')
  have hpos : 1 ≤ D.g := hg ▸ x.g_pos
  let x' : KeyIn ℂ := ⟨P', hpos, r₂, hr₂, th', hne, v', hbasis⟩
  have hg' : x'.P.g = x.P.g := hg.symm
  have hO : KeyOver (σ.comp (algebraMap (𝓞 L) L)) D.t th x' (fun i => v (i.cast hg')) := by
    refine ⟨a.φ, he₂, idIso _, a.cart, idIso_isGen hL₂, fun p => hr₂ p.1 p.2,
      KeyPow.appLE_eq_of_stalk _ th th' (hth' _ (𝟙 _)), fun i => (hv'1 i).trans ?_⟩
    rw [hve]
    rfl
  have hPB : KeyPB x' x σ := keyPB_of_keyOver _ σ D.t th x x' v _ hg' (fun _ => rfl) hov hO
  have hκ : (κ ℂ x' : ℂ) = σ (κ L x : L) := hF L ℂ σ x x' hPB
  have ex0 : (a.u.ex 0).left = eSec a.A := by
    have h₀ : a.u.ex 0 = 1 := by
      have h := a.u.ex_add 0 0
      rw [add_zero] at h
      exact mul_eq_left.1 h.symm
    have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ a.A) = η[a.A] := by rw [Hom.one_def]; simp
    rw [h₀, e₁]
    rfl
  have hRig : a.u.IsRig x'.rig := by
    intro j hj
    have hle := rigPull_le a.φ (emb σ) he₂ D.t.PP.L j
    have h₀ : ⊤ ≤ ((a.u.ex 0).left ≫ a.φ) ⁻¹ᵁ D.t.PP.L.U (j PUnit.unit PUnit.unit) := by
      rw [ex0]
      intro p hp
      exact Set.mem_iInter.1 (Set.mem_iInter.1 (hj hp) PUnit.unit) PUnit.unit
    refine (a.rig (j PUnit.unit PUnit.unit) h₀).trans ?_
    have h₁ : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((D.t.PP.L.pull a.φ).pull (eSec a.A)).U j := hj
    rw [valF_eq_valAt']
    refine Eq.trans ?_ (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) hle h₁ _).symm
    refine Eq.trans ?_ (PullbackSections.valAt'_comp (𝟙 (Sp ℂ)) (emb σ) _ _).symm
    rw [Category.id_comp]
    rfl
  have hFn : a.u.IsFn x'.th θ := by
    intro i z hz
    have hz' : ⊤ ≤ a.pt z ⁻¹ᵁ D.t.PP.L.U (i PUnit.unit) := fun p hp =>
      (mem_pull (F := a.φ) (x := (a.u.ex z).left p)).1 (hz hp)
    have h := hθ (i PUnit.unit) z hz'
    rw [pow_one] at h
    refine Eq.trans ?_ h
    have hle : (D.t.PP.L.pull a.φ).U i ≤ a.φ ⁻¹ᵁ D.t.PP.L.U (i PUnit.unit) := fun y hy => mem_pull.1 hy
    have e₁ : th'.f i = (a.φ.appLE _ _ hle).hom (th.f (i PUnit.unit)) := fn_ext fun y hy => by
      refine ((hthe _ y (hle hy)).symm).trans ?_
      have h₂ := gs_appLE a.φ _ _ hle (𝟙 _) y hy (th.f (i PUnit.unit))
      rw [Category.id_comp] at h₂
      exact h₂.symm
    show valAt' (a.u.ex z).left _ (th'.f i) = _
    rw [e₁, valAt'_appLE _ _ _ _ hle hz, valF_eq_valAt', hss (i PUnit.unit)]
    exact TB.ValAt.valAt'_res _ _ hz' _
  have key := hA x' a.u a.Hm W a.χ θ Fd _ _ a.ah hRig hFn hv'2 hFd rfl rfl
  have hint : (∫ w in Fd, a.nrm 1 θ w ^ 2) =
      ∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ a.Hm.mulVec (star z)).re) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (a.herm w w).re)) ^ 2 = _
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    simp only [ArchFrame.herm]
    push_cast
    ring
  beta_reduce at key
  simp only [_root_.mul_one] at key
  rw [hκ] at key
  rw [hint]
  exact key

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch
