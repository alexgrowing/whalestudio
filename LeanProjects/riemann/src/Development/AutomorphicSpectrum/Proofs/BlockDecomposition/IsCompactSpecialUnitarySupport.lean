import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.CompactSingles

open GlobalTheory.CompanionTheory.StrongApproxSub GlobalTheory.CompanionTheory.Sa2Prod

section Idem

variable {F : Type} [Field F] [NumberField F]

theorem place_ext {a b : AF F} (h1 : ∀ w, fstA F a w = fstA F b w)
    (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b :=
  adele_ext (ainf_ext h1) (finAdele_ext h2)

theorem fst_mul (a b : AF F) (w : InfinitePlace F) : fstA F (a * b) w = fstA F a w * fstA F b w := by
  rw [map_mul]; rfl

theorem fst_add (a b : AF F) (w : InfinitePlace F) : fstA F (a + b) w = fstA F a w + fstA F b w := by
  rw [map_add]; rfl

theorem snd_mul (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (sndA F (a * b)) = evalV F v (sndA F a) * evalV F v (sndA F b) := by
  rw [map_mul, map_mul]

theorem snd_add (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (sndA F (a + b)) = evalV F v (sndA F a) + evalV F v (sndA F b) := by
  rw [map_add, map_add]

theorem idem_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {a : AF F}
    (h : IsPlacesIdem S₁ S₂ a) : a * a = a := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_mul]
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · rw [snd_mul]
    by_cases hv : v ∈ S₂
    · rw [h.2.2.1 v hv, one_mul]
    · rw [h.2.2.2 v hv, zero_mul]

theorem idem_orth {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂) :
    a * b = 0 := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_mul, map_zero]
    by_cases hw : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ hw), mul_zero]; rfl
    · rw [ha.2.1 w hw, zero_mul]; rfl
  · rw [snd_mul, map_zero, map_zero]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv), mul_zero]
    · rw [ha.2.2.2 v hv, zero_mul]

theorem idem_add {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) : δ = a + b := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_add]
    by_cases hw : w ∈ A₁
    · rw [hδ.1 w (Finset.mem_union_left _ hw), ha.1 w hw, hb.2.1 w (Finset.disjoint_left.1 h₁ hw), add_zero]
    · rw [ha.2.1 w hw, zero_add]
      by_cases hw' : w ∈ B₁
      · rw [hδ.1 w (Finset.mem_union_right _ hw'), hb.1 w hw']
      · rw [hδ.2.1 w (by simp [hw, hw']), hb.2.1 w hw']
  · rw [snd_add]
    by_cases hv : v ∈ A₂
    · rw [hδ.2.2.1 v (Finset.mem_union_left _ hv), ha.2.2.1 v hv, hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv),
        add_zero]
    · rw [ha.2.2.2 v hv, zero_add]
      by_cases hv' : v ∈ B₂
      · rw [hδ.2.2.1 v (Finset.mem_union_right _ hv'), hb.2.2.1 v hv']
      · rw [hδ.2.2.2 v (by simp [hv, hv']), hb.2.2.2 v hv']

theorem idem_empty {δ : AF F} (h : IsPlacesIdem (∅ : Finset (InfinitePlace F)) ∅ δ) : δ = 0 := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [h.2.1 w (Finset.notMem_empty w)]; rfl
  · rw [h.2.2.2 v (Finset.notMem_empty v), map_zero, map_zero]

end Idem

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem HA_ext {g h : HA (AF F) σ J} (e : mt g = mt h) : g = h :=
  Subtype.ext (Units.ext e)

theorem SUSupp_zero_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    SUSupp σ J (0 : AF F) = {1} := by
  ext g
  constructor
  · intro hg
    refine HA_ext ?_
    have h := (mem_SUSupp.1 hg).2
    rw [map_zero, zero_smul] at h
    rw [mt_one]
    exact (sub_eq_zero.1 h.symm)
  · rintro rfl
    exact (suppGroup σ J 0).one_mem

theorem SUSupp_mono {a b : AF F} (h : b * a = a) : SUSupp σ J a ⊆ SUSupp σ J b := by
  intro g hg
  obtain ⟨h1, h2⟩ := mem_SUSupp.1 hg
  refine mem_SUSupp.2 ⟨h1, ?_⟩
  rw [← h2, smul_smul, ← map_mul, h]

theorem SUSupp_add (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) {a b : AF F} (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) :
    SUSupp σ J (a + b) = (fun p : HA (AF F) σ J × HA (AF F) σ J => p.1 * p.2) '' (SUSupp σ J a ×ˢ SUSupp σ J b) := by
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have ha' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) a =
      algebraMap (AF F) (AF F ⊗[F] E) a := by rw [← map_mul, ha]
  have hb' : algebraMap (AF F) (AF F ⊗[F] E) b * algebraMap (AF F) (AF F ⊗[F] E) b =
      algebraMap (AF F) (AF F ⊗[F] E) b := by rw [← map_mul, hb]
  ext g
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := mem_SUSupp.1 hg
    refine ⟨(truncHA σ J ha' g, truncHA σ J hb' g), ⟨truncHA_mem σ J ha' h1, truncHA_mem σ J hb' h1⟩, ?_⟩
    refine HA_ext ?_
    change trunc _ (mt g) * trunc _ (mt g) = mt g
    have hab' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) b = 0 := by
      rw [← map_mul, hab, map_zero]
    have h3 : algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1) + algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1) =
        mt g - 1 := by
      rw [← add_smul, ← map_add]; exact h2
    have e : trunc (algebraMap (AF F) (AF F ⊗[F] E) a) (mt g) * trunc (algebraMap (AF F) (AF F ⊗[F] E) b) (mt g) =
        1 + (algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1) + algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1)) := by
      have hz : (algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1)) * (algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1)) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hab', zero_smul]
      unfold trunc
      simp only [add_mul, mul_add, one_mul, mul_one, hz, add_zero]
      abel
    rw [e, h3]
    abel
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxa : (a + b) * a = a := by rw [add_mul, ha, hba, add_zero]
    have hyb : (a + b) * b = b := by rw [add_mul, hb, hab, zero_add]
    exact (suppGroup σ J (a + b)).mul_mem (SUSupp_mono hxa hx) (SUSupp_mono hyb hy)

end Group

section Compact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem isCompact_add {a b : AF F} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hca : IsCompact (SUSupp σ J a)) (hcb : IsCompact (SUSupp σ J b)) : IsCompact (SUSupp σ J (a + b)) := by
  haveI := topGroup σ J
  rw [SUSupp_add σ J ha hb hab]
  exact (hca.prod hcb).image continuous_mul

theorem isCompact_fin (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ {δ : AF F}, IsPlacesIdem (∅ : Finset (InfinitePlace F)) T₂ δ →
      (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  classical
  induction T₂ using Finset.induction_on with
  | empty =>
    intro δ hδ _
    rw [idem_empty hδ, SUSupp_zero_eq]
    exact isCompact_singleton
  | insert v T hv ih =>
    intro δ hδ hc
    obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    obtain ⟨d, hd⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ T
    have h₁ : Disjoint (∅ : Finset (InfinitePlace F)) ∅ := Finset.disjoint_empty_left _
    have h₂ : Disjoint ({v} : Finset (HeightOneSpectrum (𝓞 F))) T := Finset.disjoint_singleton_left.2 hv
    have hδ' : IsPlacesIdem ((∅ : Finset (InfinitePlace F)) ∪ ∅) ({v} ∪ T) δ := by
      rwa [Finset.empty_union, ← Finset.insert_eq]
    rw [idem_add he hd h₁ h₂ hδ']
    exact isCompact_add (idem_self he) (idem_self hd) (idem_orth he hd h₁ h₂)
      (hc v (Finset.mem_insert_self v T) e he) (ih hd fun u hu => hc u (Finset.mem_insert_of_mem hu))

theorem isCompact_all (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (T₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (h₂ : ∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e))
    (T₁ : Finset (InfinitePlace F)) :
    ∀ {δ : AF F}, IsPlacesIdem T₁ T₂ δ →
      (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  classical
  induction T₁ using Finset.induction_on with
  | empty =>
    intro δ hδ _
    exact isCompact_fin σ J T₂ hδ h₂
  | insert w T hw ih =>
    intro δ hδ hc
    obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    obtain ⟨d, hd⟩ := StrongApprox.exists_isPlacesIdem (F := F) T T₂
    have d₁ : Disjoint ({w} : Finset (InfinitePlace F)) T := Finset.disjoint_singleton_left.2 hw
    have d₂ : Disjoint (∅ : Finset (HeightOneSpectrum (𝓞 F))) T₂ := Finset.disjoint_empty_left _
    have hδ' : IsPlacesIdem ({w} ∪ T) ((∅ : Finset (HeightOneSpectrum (𝓞 F))) ∪ T₂) δ := by
      rwa [Finset.empty_union, ← Finset.insert_eq]
    rw [idem_add he hd d₁ d₂ hδ']
    exact isCompact_add (idem_self he) (idem_self hd) (idem_orth he hd d₁ d₂)
      (hc w (Finset.mem_insert_self w T) e he) (ih hd fun u hu => hc u (Finset.mem_insert_of_mem hu))

end Compact

theorem compact_of_singles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ →
    (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) →
    (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  intro F E _ _ _ _ _ σ _ M J T₁ T₂ δ hδ h₁ h₂
  exact isCompact_all σ J T₂ h₂ T₁ hδ h₁

end GlobalTheory.CompanionTheory.SaGen.CompactSingles

end
