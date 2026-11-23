import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter

noncomputable section

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_twistSys {n : ℕ} (b : Fin n → ℤ) (l : List (Fin n)) (a : ℤ) :
    l.foldl (fun F i => F.twist (twistSys S x (b i))) (twistSys S x a) =
      twistSys S x (a + (l.map b).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, twistSys_twist_eq_add, ih, List.map_cons, List.sum_cons, add_assoc]

theorem tensorSub_twistSys {n : ℕ} (b : Fin n → ℤ) (T : Finset (Fin n)) :
    tensorSub (fun i => twistSys S x (b i)) T = twistSys S x (∑ i ∈ T, b i) := by
  classical
  rw [tensorSub, foldl_twist_twistSys, zero_add,
    ← List.sum_toFinset b ((List.nodup_finRange n).filter _)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp

theorem interSum_twistSys (pp : Ideal (Poly S N)) {n : ℕ} (b : Fin n → ℤ) (c : ℕ) :
    interSum pp (fun i => twistSys S x (b i)) c =
      ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * restrLen pp (twistSys S x (∑ i ∈ T, b i + c)) := by
  unfold interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [tensorSub_twistSys, twistSys_twist_eq_add]

end Lemmas

section Differences

variable {K : Type*}

theorem foldr_diffStep_eq {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (m : K → ℤ) :
    (l.map bs).foldr NumbersDVR.diffStep h m =
      ∑ T ∈ l.toFinset.powerset, (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have ha' : a ∉ l.toFinset := fun h' => ha (List.mem_toFinset.mp h')
    rw [List.map_cons, List.foldr_cons, List.toFinset_cons, Finset.sum_powerset_insert ha']
    change (l.map bs).foldr NumbersDVR.diffStep h m - (l.map bs).foldr NumbersDVR.diffStep h (m - bs a) = _
    rw [ih hl' m, ih hl' (m - bs a), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h' => ha' (Finset.mem_powerset.mp ht h')
    rw [Finset.card_insert_of_notMem hat, Finset.sum_insert hat, pow_succ, sub_sub]
    ring

theorem mixedDiff_eq_sum {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    NumbersDVR.mixedDiff bs h m = ∑ T : Finset (Fin n), (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  rw [NumbersDVR.mixedDiff, List.ofFn_eq_map, foldr_diffStep_eq bs h _ (List.nodup_finRange n),
    List.toFinset_finRange, Finset.powerset_univ]

end Differences

section Point

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ}

theorem restrLen_primeOf_eq_finrank (y : Fin (N + 1) → K') {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y K') : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

end Point

theorem NumEq.proof (hRL : RestrLenRestrict.Statement.{0, 0}) : NumEq.Statement := by
  intro k _ N Ω _ _ x pp e b hsub
  classical

  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)

  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)

  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]

  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h

  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B) (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega),
      mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
