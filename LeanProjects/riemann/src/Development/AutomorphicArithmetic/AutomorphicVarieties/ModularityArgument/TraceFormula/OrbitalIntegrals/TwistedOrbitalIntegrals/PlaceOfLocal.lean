import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets in
private theorem key (hT : GLTop) (hC : ExtCont) (hCC : CentComm) (hH : HaarComm) (hI : TwCentImg) (hG : GeoOfMatch) (hX : GeoTransport)
    (hA : AlongIndep) (k E S : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E) (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (e : S ≃+* E) (he : Continuous e) (he' : Continuous e.symm)
    (ι : k →+* S) (t₀ : S →+* S) (h1 : ∀ x, e (ι x) = algebraMap k E x) (h2 : ∀ y, e (t₀ y) = (s : E →+* E) (e y))
    (n : ℕ) [MeasurableSpace (GL (Fin n) S)] [BorelSpace (GL (Fin n) S)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (mE : Measure (GL (Fin n) S)) (mF : Measure (GL (Fin n) k)) (hE : mE.IsHaarMeasure) (hF : mF.IsHaarMeasure)
    [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] :
    (mE.map (mapGL n (e : S →+* E))).IsHaarMeasure ∧ ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k),
      Match s (mE.map (mapGL n (e : S →+* E))) mF φ f →
      PositivityTheory.Rg.Tf.Geo.Match ι t₀ (Module.finrank k E) mE mF 1 (fun g => φ (mapGL n (e : S →+* E) g)) f := by
  obtain ⟨x1, x2⟩ := hX _ _ _ e he he' ι (algebraMap k E) t₀ (s : E →+* E) h1 h2 n (Module.finrank k E) mE mF
  have hμ := x1 hE
  refine ⟨hμ, fun φ hφ f hf hM γ hγ ν hν => ?_⟩
  have hM' := hG k E s hs n _ mF hμ hF φ hφ f hf hM γ hγ ν hν
  obtain ⟨y1, y2⟩ := x2 γ
  have hl : ∀ x, mapGL n (e.symm : E →+* S) (mapGL n (e : S →+* E) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
  have hrt : ∀ x, mapGL n (e : S →+* E) (mapGL n (e.symm : E →+* S) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  refine ⟨fun δ hδ => ?_, fun hn => hM'.2 fun ⟨δ', h'⟩ => hn ⟨mapGL n (e.symm : E →+* S) δ', (y1 _).2 (by rw [hrt]; exact h')⟩⟩
  have hδ' := (y1 δ).1 hδ
  rw [← hM'.1 _ hδ']
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  obtain ⟨c1, c2⟩ := cent_facts hCC hγ
  obtain ⟨s1, s2, -⟩ := hH _ _ c1 c2 ν hν
  obtain ⟨d1, d2⟩ := (hC k E).2.2 n
  set δ' := mapGL n (e : S →+* E) δ with hδe
  have hS := (hI k E s hs n δ' γ hγ hδ').2
  let Φ : GL (Fin n) E → ℂ := fun x => φ (twConj (sigmaGL s) x δ')
  have hΦc : Continuous Φ := hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul (d2 s))
  have hΦe : ∀ x, φ (mapGL n (e : S →+* E) (x⁻¹ * δ * mapGL n t₀ x)) =
      Φ (mapGL n (e : S →+* E) x) := fun x => by
    rw [map_mul, map_mul, map_inv]
    refine congrArg (fun z => φ ((mapGL n (e : S →+* E) x)⁻¹ * δ' * z)) (?_ : mapGL n (e : S →+* E) (mapGL n t₀ x) = sigmaGL s (mapGL n (e : S →+* E) x))
    exact Units.ext (Matrix.ext fun i j => h2 _)
  unfold PositivityTheory.Rg.Tf.Geo.twOrb
  simp only [hΦe]
  by_cases hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id
      (fun t : Subgroup.centralizer {γ} => mapGL n ι (t : GL (Fin n) k)) ν ρ
  · have hρ := (y2 ν fun g => hex.choose (mapGL n (e.symm : E →+* S) g)).1.2 (by simp only [hl]; exact hex.choose_spec)
    haveI : MeasurableInv (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) :=
      ⟨(measurable_subtype_coe.inv).subtype_mk⟩
    have k1 := hA _ _ (mE.map (mapGL n (e : S →+* E))) ν
      ((incl : GL (Fin n) k →* GL (Fin n) E).comp (Subgroup.centralizer {γ}).subtype)
      (d1.measurable.comp measurable_subtype_coe) Φ hΦc.measurable
      (fun t g => congrArg φ (twConj_mul_left _ _ (hS ▸ ⟨t, t.2, rfl⟩) g)) _ hρ
    refine Eq.trans ?_ k1.symm
    rw [(y2 ν _).2, PositivityTheory.Rg.Tf.Geo.quotInt, dif_pos hex]
    simp only [hl, id]
  · rw [PositivityTheory.Rg.Tf.Geo.quotInt, dif_neg hex, PositivityTheory.Rg.Tf.Geo.quotInt, dif_neg fun ⟨ρ', h'⟩ => hex ⟨_, (y2 ν ρ').1.1 h'⟩]

theorem UpperTheory.V.Z.Tf.Orb.placeOfLocal :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.GeoOfMatch → UpperTheory.V.Z.Tf.Orb.GeoTransport → UpperTheory.V.Z.Tf.Orb.AlongIndep → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal := by
  intro hT hC hCC hH hI hG hX hA F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  let e : CompletionsOver E v ≃+* w.1.adicCompletion E := RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E
  have he : Continuous e := continuous_apply w
  have he' : Continuous e.symm := (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous
  rw [← hr]
  exact @key hT hC hCC hH hI hG hX hA _ _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 s hs _ _ _ e he he' _ _ h1 h2 n _ _ _ _ mE mF hE hF _ _
