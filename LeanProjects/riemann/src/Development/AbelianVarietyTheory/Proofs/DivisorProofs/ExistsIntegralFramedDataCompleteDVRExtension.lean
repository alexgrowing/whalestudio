import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

noncomputable section

namespace GlobalTheory.FramedExt

theorem eSec_hom {S : Scheme.{0}} (X : Over S) [GrpObj X] : eSec X ≫ X.hom = 𝟙 _ := by
  simp [eSec]

theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_ext {R R' : Type} [CommRing R] [CommRing R'] (F₁ F₂ : DualNumber R →+* DualNumber R')
    (h : ∀ a : R, F₁ (algebraMap R (DualNumber R) a) = F₂ (algebraMap R (DualNumber R) a))
    (hε : F₁ DualNumber.eps = F₂ DualNumber.eps) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  have hx : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hx, map_add, map_add, map_mul, map_mul, h, h, hε]

theorem generates_of_flat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R R₂ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R₂] [IsDomain R₂] (φ : R →+* R₂) (hφ : Function.Injective φ) (G : SAB H (Sp R)) (G₂ : SAB H (Sp R₂)) (m : SABMap G₂ G (spMap φ)) (wI : G₂.PP.L.Iso (G.PP.L.pull m.φ)) (hwI : LB.Gen.IsGen wI) (θ : G.PP.L.Sec) (θ₂ : G₂.PP.L.Sec) (hθ : IsoMaps wI θ₂ (thfPull G.PP.L m.φ θ)) : Generates (X := G.G) θ → Generates (X := G₂.G) θ₂ := by
  intro hgen
  letI := φ.toAlgebra
  have : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat R R₂ := inferInstance
  haveI : IsSeparated G.G.hom := G.semi.separated
  haveI : QuasiCompact G.G.hom := G.semi.quasiCompact
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  have hinter : ∀ U W : G.G.left.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal G.G.hom)) ⊤
      (isAffineOpen_top _) U le_top W le_top hU hW
  have Hpb : IsPullback m.φ G₂.G.hom G.G.hom (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) := m.cart.1
  exact fun s' => ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso G.G.hom G₂.G.hom m.φ Hpb hinter G.PP.L G.PP.isLB θ hgen
    G₂.PP.L G₂.PP.isLB wI hwI θ₂ _ hθ (fun _ _ => rfl) s'

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (k : KeyIn R') (k' : KeyIn R'') (f : R →+* R') (g : R' →+* R'') : IsFibreOf k G L rig θ w f → KeyPB k' k g → IsFibreOf k' G L rig θ w (g.comp f) := by
  intro H H'
  obtain ⟨φ, he, w₀, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g₀ := (isGen_iff w₀).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp k.P.isLB w₀ w' g₀ g' hL k'.P.isLB
  have he'' : eSec k'.P.A ≫ φ' ≫ φ = spMap (g.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f g).symm rfl,
    (isGen_iff w'').2 (T.pgen_comp k.P.isLB g₀ g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₀ _ (fun _ => eSec G) _ k.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec k.P.A) _ k'.rig k.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' k.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp k.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ k'.rig rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (g.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk w'' θ k'.th fun z j k₀ hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart k.P.isLB (φ' z)
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq w₀ θ k.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq w' k.th k'.th hs' (𝟙 _) z i k₀ hi hk
    rw [T _ (𝟙 _) z j i k₀ hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem isFibreOf_descend {R R₂ K : Type} [CommRing R] [CommRing R₂] [CommRing K] (φ : R →+* R₂) (f : R₂ →+* K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (L₂ : LB G₂.left) (hL₂ : L₂.IsLB) (rig₂ : (L₂.pull (eSec G₂)).Gen) (ψ : G₂.left ⟶ G.left) (hψ : IsGrpPullback G₂ G (spMap φ) ψ) (he : eSec G₂ ≫ ψ = spMap φ ≫ eSec G) (wI : L₂.Iso (L.pull ψ)) (hwI : LB.Gen.IsGen wI) (hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂) fun _ => 1) rig₂ (rigPullOf ψ (spMap φ) he L rig)) (θ : L.Sec) (θ₂ : L₂.Sec) (hθ : IsoMaps wI θ₂ (thfPull L ψ θ)) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (w₂ : Fin n → (epsR R₂ ⟶ G₂)) (hw : ∀ i, (w₂ i).left ≫ ψ = spMap (Chart.dualMapR φ) ≫ (w i).left) (k : KeyIn K) : IsFibreOf k G L rig θ w (f.comp φ) → IsFibreOf k G₂ L₂ rig₂ θ₂ w₂ f := by
  intro H
  obtain ⟨φk, hek, e, hg, F, hp, hgen, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨ψ₂, hfac, hbase⟩ : ∃ ψ₂ : k.P.A.left ⟶ G₂.left, ψ₂ ≫ ψ = φk ∧ ψ₂ ≫ G₂.hom = k.P.A.hom ≫ spMap f :=
    ⟨hψ.1.lift φk (k.P.A.hom ≫ spMap f) (by rw [hp.1.w, spMap_comp, Category.assoc]),
      hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  subst hfac
  have hp₂ : IsGrpPullback k.P.A G₂ (spMap f) ψ₂ := hψ.cancel (hp.congr (spMap_comp φ f) rfl) hbase
  have he₂ : eSec k.P.A ≫ ψ₂ = spMap f ≫ eSec G₂ := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, hek, Category.assoc, he, spMap_comp, Category.assoc]
    · rw [Category.assoc, hbase, ← Category.assoc, eSec_hom, Category.assoc, eSec_hom]
      simp
  have gI := (isGen_iff wI).1 hwI
  have g₀ := (isGen_iff e).1 hgen
  obtain ⟨e₂, T⟩ := exists_cancel hL wI e gI g₀ hL₂ k.P.isLB
  have hFe : F = (Chart.dualMapR f).comp (Chart.dualMapR φ) := dual_ext _ _ (fun a => by
      simp only [hF, RingHom.comp_apply]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hε]; ext <;> simp [Chart.dualMapR])
  refine ⟨ψ₂, he₂, e₂, hg, Chart.dualMapR f, hp₂, (isGen_iff e₂).2 (T.pgen_cancel hL gI g₀), ?_, ?_,
    fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff wI _ (fun _ => eSec G) _ rig₂ rig (spMap φ) _
      (rigPull_le ψ (spMap φ) he L) (fun _ => rfl)).1 hrig
    have r'' := (maps_iff e _ (fun _ => eSec G) _ k.rig rig (spMap (f.comp φ)) _
      (rigPull_le (ψ₂ ≫ ψ) (spMap (f.comp φ)) hek L) (fun _ => rfl)).1 hr
    rw [spMap_comp] at r''
    have r₂ := T.pmaps_cancel hL (fun _ => he₂) r₀ r''
    exact (maps_iff e₂ _ (fun _ => eSec G₂) _ k.rig rig₂ (spMap f) _
      (rigPull_le ψ₂ (spMap f) he₂ L₂) (fun _ => rfl)).2 r₂
  · have hθ' : ∀ (j : (L.pull ψ).ι) (i : L₂.ι) (hle : (L.pull ψ).U j ⊓ L₂.U i ≤ ψ ⁻¹ᵁ L.U (j PUnit.unit)),
        (Scheme.Hom.appLE ψ (L.U (j PUnit.unit)) ((L.pull ψ).U j ⊓ L₂.U i) hle).hom (θ.f (j PUnit.unit)) =
          (show Γ(G₂.left, (L.pull ψ).U j ⊓ L₂.U i) from (wI.s (j, i)).val) * resG _ inf_le_right (θ₂.f i) := by
      intro j i hle
      refine Eq.trans ?_ (hθ j i)
      dsimp only [thfPull]
      first
        | (erw [Scheme.Hom.appLE_map])
        | (simp only [Scheme.Hom.appLE_map])
        | (rw [← Scheme.Hom.appLE_map ψ _ (homOfLE inf_le_left).op]; rfl)
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk e₂ θ₂ k.th fun z j k₀ hj hk => ?_
    obtain ⟨jL, hjL⟩ := exists_chart hL (ψ (ψ₂ z))
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq e θ k.th hs (𝟙 _) z jL k₀ hjL hk
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq wI θ θ₂ hθ' (𝟙 _ ≫ ψ₂) z jL j hjL hj
    rw [Category.assoc] at b
    rw [T _ (𝟙 _) z jL j k₀ hjL hj hk, b, Units.val_mul, _root_.mul_assoc] at a
    exact (Units.mul_right_inj _).1 a
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, hv i, Category.assoc, hw, ← Category.assoc, hFe, spMap_comp]
    · rw [Category.assoc, hbase, ← Category.assoc, Over.w (k.v i), Category.assoc, Over.w (w₂ (Fin.cast hg i))]
      simp only [epsR, Over.mk_hom]
      rw [← spMap_comp, ← spMap_comp, dualMapR_comp_algebraMap]

theorem exists_framed_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  intro E _ _ _ H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  have hφ' : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ']
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨m2', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ G.G G₂.G m.φ m.cart G.semi.smooth n w hw
  obtain ⟨k', hk'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring k iT
  obtain ⟨wI, hwI, hrI, -⟩ := m.lin
  obtain ⟨θ₂, hθ₂⟩ := GlobalTheory.ArcQ.NormalForm.exists_isoMaps wI hwI G.PP.isLB G₂.PP.isLB (thfPull G.PP.L m.φ θ)
  have he : eSec G₂.G ≫ m.φ = spMap φ ≫ eSec G.G := m.cm.e_comm.trans (congrArg (· ≫ eSec G.G) m.base)
  have hr : ∀ (e : Sp T'.V ⟶ Sp T.V) (_ : m.cm.e = e) (he : eSec G₂.G ≫ m.φ = e ≫ eSec G.G),
      rigPullOf m.φ e he G.PP.L G.PP.rig = m.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  have hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂.G) fun _ => 1) G₂.PP.rig
      (rigPullOf m.φ (spMap φ) he G.PP.L G.PP.rig) := by
    rw [hr _ m.base he]; exact hrI
  have h1 := isFibreOf_trans G.G G.PP.L G.PP.isLB G.PP.rig θ w k k' (algebraMap T.V T.Fr) iT hk hk'
  rw [← hφ'] at h1
  have hinj : Function.Injective φ := fun a b hab => IsFractionRing.injective T.V T.Fr
    (iT.injective (by rw [← hφ a, ← hφ b, hab]))
  exact ⟨G₂, t₂, p, m2', n, w', θ₂, k', hw', generates_of_flat φ hinj G G₂ m wI hwI θ θ₂ hθ₂ hθ,
    isFibreOf_descend φ (algebraMap T'.V T'.Fr) G.G G₂.G G.PP.L G.PP.isLB G.PP.rig G₂.PP.L G₂.PP.isLB G₂.PP.rig m.φ
      m.cart he wI hwI hrig θ θ₂ hθ₂ w w' hww k' h1, hk'⟩

end GlobalTheory.FramedExt
