import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Crt

theorem mem_sup_prod_smul {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T N : Submodule R M)
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) {y : M} (hy : y ∈ N) (s : Finset ι)
    (h : ∀ i ∈ s, y ∈ T ⊔ I i • N) : y ∈ T ⊔ (∏ i ∈ s, I i) • N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.mem_sup_right hy
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hc : IsCoprime (I i) (∏ j ∈ s, I j) :=
      IsCoprime.prod_right fun j hj => hI i j (fun e => hi (e ▸ hj))
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
    have key : ∀ (A B : Ideal R) (c : R), c ∈ A → y ∈ T ⊔ B • N → c • y ∈ T ⊔ (A * B) • N := by
      intro A B c hc hy
      obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine Submodule.add_mem_sup (T.smul_mem c ht) ?_
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hc hz
    have e : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine Submodule.add_mem _ (key _ _ a ha h2) ?_
    rw [mul_comm]
    exact key _ _ b hb h1

theorem mem_sup_smul_mono {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {T N : Submodule R M}
    {I J : Ideal R} (h : I ≤ J) {y : M} (hy : y ∈ T ⊔ I • N) : y ∈ T ⊔ J • N :=
  (sup_le_sup_left (Submodule.smul_mono_left h) T : T ⊔ I • N ≤ T ⊔ J • N) hy

theorem prod_le_span {O : Type*} [CommRing O] [IsDedekindDomain O] {g : O} (hg : g ≠ 0)
    (hsq : ∀ w : HeightOneSpectrum O, g ∉ w.asIdeal ^ 2) (s : Finset (HeightOneSpectrum O))
    (hs : ∀ w : HeightOneSpectrum O, g ∈ w.asIdeal → w ∈ s) :
    ∏ w ∈ s, w.asIdeal ≤ Ideal.span {g} := by
  have h0 : (Ideal.span {g} : Ideal O) ≠ ⊥ := fun e => hg (Ideal.span_singleton_eq_bot.1 e)
  have hsf : Squarefree (Ideal.span {g} : Ideal O) := by
    refine (squarefree_iff_no_irreducibles (x := (Ideal.span {g} : Ideal O)) h0).2 ?_
    intro x hx hd
    have hp : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.1 hx
    refine hsq ⟨x, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ?_
    rw [Ideal.dvd_span_singleton, ← pow_two] at hd
    exact hd
  have hrad : (Ideal.span {g}).radical ≤ Ideal.span {g} := by
    rintro x ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsf.isRadical n _ hn
  refine le_trans ?_ hrad
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP1, hP2⟩
  have hP0 : P ≠ ⊥ := fun e => h0 (le_bot_iff.1 (hP1.trans e.le))
  have hm := hs ⟨P, hP2, hP0⟩ ((Ideal.span_singleton_le_iff_mem _).1 hP1)
  have hle : ∏ w ∈ s, w.asIdeal ≤ (⟨P, hP2, hP0⟩ : HeightOneSpectrum O).asIdeal :=
    (Ideal.prod_le_inf (s := s) (f := fun w : HeightOneSpectrum O => w.asIdeal)).trans (Finset.inf_le hm)
  exact hle

variable {D : D7}

theorem g_not_mem_sq (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  intro hm
  have hc : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have key : ∀ k (b : 𝓞 D.host.E), IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) b →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) * b ∈ w.asIdeal ^ 2 → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    rintro k b ⟨u, v, huv⟩ h hk
    refine (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.1 ?_
    have e : ((D.host.g k : ℕ) : 𝓞 D.host.E) =
        u * ((D.host.g k : ℕ) : 𝓞 D.host.E) ^ 2 + v * (((D.host.g k : ℕ) : 𝓞 D.host.E) * b) := by
      linear_combination (-((D.host.g k : ℕ) : 𝓞 D.host.E)) * huv
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hk 2)) (Ideal.mul_mem_left _ _ h)
  rw [Nat.cast_mul] at hm
  rcases w.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero hm) with h | h
  · exact key 0 _ hc hm h
  · exact key 1 _ hc.symm (mul_comm (G := 𝓞 D.host.E) _ _ ▸ hm) h

def toInt (I : Formalism.MainNotions.S.AutInst) : 𝓞 I.E →+* Formalism.MainNotions.S.IntAf I.F I.E :=
  ((Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).comp (algebraMap (𝓞 I.E) I.E)).codRestrict _ fun t =>
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 I.E) I.E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem toInt_smul (I : Formalism.MainNotions.S.AutInst) (a : 𝓞 I.E) (y : Fin I.n → I.E) :
    toInt I a • incl I y = incl I ((a : I.E) • y) := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a : I.E) * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i) =
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((a : I.E) * y i)
  rw [map_mul]

def hostInt (X : HidaSetting D) : 𝓞 D.host.E →+* Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  (toInt X.B.I).comp (RingOfIntegers.mapRingEquiv X.ιE.symm).toRingHom

theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    wLf X w = (w.asIdeal.map (hostInt X)) • X.B.I.Lf := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    show incl X.B.I x ∈ (w.asIdeal.map (hostInt X)) • X.B.I.Lf
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ⟨b, hb, hab⟩, y, hy, rfl⟩ := hz
      rw [← toInt_smul]
      have : toInt X.B.I a = hostInt X b := by
        refine congrArg (toInt X.B.I) (RingOfIntegers.ext ?_)
        show (a : X.B.I.E) = X.ιE.symm (b : D.host.E)
        rw [← hab, RingEquiv.symm_apply_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    | zero =>
      have : incl X.B.I 0 = 0 := funext fun i => map_zero _
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : incl X.B.I (x + y) = incl X.B.I x + incl X.B.I y := funext fun i => map_add _ _ _
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : incl X.B.I (a • x) = toInt X.B.I a • incl X.B.I x := (toInt_smul _ a x).symm
      rw [this]; exact Submodule.smul_mem _ _ hx
  · unfold Ideal.map
    rw [show X.B.I.Lf = Submodule.span _ (Set.range fun x : X.B.I.L => incl X.B.I x) from rfl]
    rw [Submodule.span_smul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    show toInt X.B.I (RingOfIntegers.mapRingEquiv X.ιE.symm b) • incl X.B.I y ∈ wLf X w
    rw [toInt_smul]
    refine Submodule.subset_span ⟨⟨_, Submodule.subset_span ⟨_, ⟨b, hb, ?_⟩, y, hy, rfl⟩⟩, rfl⟩
    exact X.ιE.apply_symm_apply _

theorem mL_eq (X : HidaSetting D) (m : ℕ) :
    mL X.B.I m = ((Ideal.span {(m : 𝓞 D.host.E)}).map (hostInt X)) • X.B.I.Lf := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_smul (r := (m : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)) (Ideal.mem_span_singleton_self _) hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)

theorem inMod_iff_forall_modW : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  intro D X _ _ S _ y hy
  unfold InMod ModW
  simp only [mL_eq, wLf_eq]
  constructor
  · intro h w hw
    exact mem_sup_smul_mono (Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).2 hw)) h
  · intro h
    have hg : ((X.B.g : ℕ) : 𝓞 D.host.E) ≠ 0 := by
      rw [X.g_eq]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hfin : {w : HeightOneSpectrum (𝓞 D.host.E) | ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal}.Finite := by
      have := Ideal.finite_factors (I := Ideal.span {((X.B.g : ℕ) : 𝓞 D.host.E)}) (by simpa using hg)
      simpa only [Ideal.dvd_span_singleton] using this
    have h1 := mem_sup_prod_smul _ _ (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.asIdeal.map (hostInt X))
      (fun i j hij => by
        rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup,
          i.isMaximal.coprime_of_ne j.isMaximal (fun e => hij (HeightOneSpectrum.ext e)), Ideal.map_top])
      hy hfin.toFinset (fun w hw => h w (hfin.mem_toFinset.1 hw))
    refine mem_sup_smul_mono ?_ h1
    have h2 := prod_le_span hg (fun w => by rw [X.g_eq]; exact g_not_mem_sq w) hfin.toFinset
      (fun w hw => hfin.mem_toFinset.2 hw)
    refine le_trans (le_of_eq ?_) (Ideal.map_mono h2)
    exact (map_prod (Ideal.mapHom (hostInt X)) _ _).symm

end GlobalTheory.Mem.GroupLoc.Crt

end
